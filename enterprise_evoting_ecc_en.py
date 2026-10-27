# -*- coding: utf-8 -*-
"""
===============================================================================
EXPERIMENTAL IMPLEMENTATION: A SECURE AND EFFICIENT ELLIPTIC CURVE E-VOTING
SOLUTION FOR ENTERPRISES (ENGLISH VERSION)
===============================================================================
Description:
    Complete reference and benchmark implementation of the proposed Enterprise
    Electronic Voting Protocol based on a 4-pass linear blind digital signature
    scheme over the 448-bit Edwards elliptic curve (Ed448 / Curve448-Goldilocks)
    coupled with the SHAKE256 extendable-output function (NIST FIPS 202).

Core Components (aligned with Table 1 and Section 4 of the English manuscript):
    1. Elliptic curve group arithmetic over Ed448 (x^2 + y^2 = 1 + d*x^2*y^2 mod p)
       using Extended Projective Coordinates (X, Y, Z, T) for fast Point Addition
       (PA) and scalar Point Multiplication (PM).
    2. Domain-separated cryptographic hash functions (H_1, H_2, H_3, H_A1, H_A2)
       instantiated from SHAKE256 by extracting 112 bytes (896 bits) per call and
       reducing modulo q to eliminate statistical bias (< 2^-448), alongside a
       56-byte keystream mask derivation function (KDF).
    3. Stage 1 (KeyGen): Generation of Signing Committee keys (d_C, Y_C),
       initialization of the empty state table T = {(ID_V, r_2)}, and registration
       of shareholder/employee identity keys (ID_V, Y_V) via Enterprise IAM.
    4. Stage 2 (Eligibility Authentication and Blind Signing - 4-Pass Protocol):
       - Pass 1 (Blind_1): Voter generates initial commitment U_1, asymmetric point
         ciphertext C_1, and the first Elliptic Curve Non-Interactive Proof of
         Secret Key Knowledge (EC-NIPoK) pi_1 = (A_1, zeta_1).
       - Pass 2 (BlindSign_1): Signing Committee Server verifies voting eligibility
         (ID_V not in T), checks EC-NIPoK pi_1, decrypts U_1, samples secret nonce
         r_2 with collision checking against state table T, records (ID_V, r_2) in T,
         and encrypts server contribution U_2 = r_2 G under Y_V into C_2.
       - Pass 3 (Blind_2): Voter decrypts U_2, performs dual-base re-randomization
         using independent scalars (u, w) to form W = U_1 + U_2 + uG + wY_C, computes
         the ballot-anchored hash chain for M, blinds the challenge as
         tilde_h_3 = (h_3 + w) mod q, and generates the second EC-NIPoK pi_2 = (A_2, zeta_2).
       - Pass 4 (BlindSign_2): Signing Committee Server verifies the atomic session,
         checks EC-NIPoK pi_2, retrieves r_2 from state table T, computes the blind
         signing response z_1 = (r_2 + tilde_h_3 d_C) mod q, derives the 56-byte mask
         kappa, outputs C_3 = kappa XOR Encode(z_1), and atomically closes the session.
       - Unblinding (Unblind): Voter recovers z_1, verifies z_1 G == U_2 + tilde_h_3 Y_C,
         and computes z = (z_1 + r_1 + u) mod q to obtain the public ballot signature
         sigma = (W, K, z).
    5. Stage 3 (Verify): Tallying Server publicly verifies z G == W + h_3 Y_C.
    6. Security verification suite (Correctness, Information-Theoretic Perfect
       Blindness Adv^blind = 0, Double-voting prevention, Nonce collision resistance,
       and Atomic Sequential Queue against polynomial ROS attacks) and benchmarking.
===============================================================================
"""

import hashlib
import secrets
import time
from dataclasses import dataclass
from typing import Dict, Tuple, Optional

# =============================================================================
# 1. 448-BIT EDWARDS ELLIPTIC CURVE PARAMETERS (Ed448 / Curve448 - RFC 8032)
# =============================================================================
# Prime finite field modulus p = 2^448 - 2^224 - 1
P_ED448: int = (1 << 448) - (1 << 224) - 1

# Untwisted Edwards curve coefficient d: x^2 + y^2 = 1 + d*x^2*y^2 (mod p)
D_ED448: int = P_ED448 - 39081

# Large prime order q of the cyclic subgroup E = <G>
Q_ED448: int = (
    (1 << 446)
    - 0x8335DC163BB124B65129C96FDE933D8D723A70AADC873D6D54A7BB0D
)

# Canonical encoding length for a scalar in Z_q: n = ceil(log2(q)/8) = 56 bytes
SCALAR_BYTES: int = 56
HASH_EXTRACT_BYTES: int = 112  # 896 bits extracted before mod q reduction

# Base point generator G = (X_G, Y_G) of prime order q on Ed448
GX_ED448: int = (
    224580040295924300187604334099896036246789641632564134246125461686950415467406032909029192869357953282578032075146446173674602635247710
)
GY_ED448: int = (
    298819210078481492676017930443930673437544040154080242095928241372331506189835876003536878655418784733982303233503462500531545062832660
)


class Ed448Point:
    """
    Elliptic curve point representation on Ed448 using Extended Projective
    Coordinates (X, Y, Z, T with x = X/Z, y = Y/Z, x*y = T/Z) following
    Bernstein and Lange (ASIACRYPT 2007) and RFC 8032.
    """
    __slots__ = ("X", "Y", "Z", "T")

    def __init__(self, X: int, Y: int, Z: int = 1, T: Optional[int] = None):
        self.X = X % P_ED448
        self.Y = Y % P_ED448
        self.Z = Z % P_ED448
        if T is None:
            inv_z = pow(self.Z, P_ED448 - 2, P_ED448)
            self.T = (self.X * self.Y * inv_z) % P_ED448
        else:
            self.T = T % P_ED448

    @classmethod
    def infinity(cls) -> "Ed448Point":
        """Identity element (point at infinity / neutral element) O = (0, 1)."""
        return cls(0, 1, 1, 0)

    def is_infinity(self) -> bool:
        """Check whether the point is the identity element O = (0, 1)."""
        return (self.X % P_ED448 == 0) and (self.Y % P_ED448 == self.Z % P_ED448)

    def to_affine(self) -> Tuple[int, int]:
        """Convert projective coordinates to canonical affine coordinates (x, y)."""
        inv_z = pow(self.Z, P_ED448 - 2, P_ED448)
        return (self.X * inv_z) % P_ED448, (self.Y * inv_z) % P_ED448

    def is_on_curve(self) -> bool:
        """Verify that the point satisfies the Ed448 curve equation."""
        x, y = self.to_affine()
        x2 = (x * x) % P_ED448
        y2 = (y * y) % P_ED448
        lhs = (x2 + y2) % P_ED448
        rhs = (1 + D_ED448 * x2 * y2) % P_ED448
        return lhs == rhs

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Ed448Point):
            return False
        # Projective equality check: X1*Z2 == X2*Z1 and Y1*Z2 == Y2*Z1 (mod p)
        return (
            (self.X * other.Z - other.X * self.Z) % P_ED448 == 0
            and (self.Y * other.Z - other.Y * self.Z) % P_ED448 == 0
        )

    def __neg__(self) -> "Ed448Point":
        """Inverse of a point on an Edwards curve: -(x, y) = (-x, y)."""
        return Ed448Point((-self.X) % P_ED448, self.Y, self.Z, (-self.T) % P_ED448)

    def __add__(self, other: "Ed448Point") -> "Ed448Point":
        """Unified Point Addition (PA) on Ed448."""
        A = (self.X * other.X) % P_ED448
        B = (self.Y * other.Y) % P_ED448
        C = (D_ED448 * self.T * other.T) % P_ED448
        D = (self.Z * other.Z) % P_ED448
        E = ((self.X + self.Y) * (other.X + other.Y) - A - B) % P_ED448
        F = (D - C) % P_ED448
        G_val = (D + C) % P_ED448
        H = (B - A) % P_ED448
        X3 = (E * F) % P_ED448
        Y3 = (G_val * H) % P_ED448
        T3 = (E * H) % P_ED448
        Z3 = (F * G_val) % P_ED448
        return Ed448Point(X3, Y3, Z3, T3)

    def __sub__(self, other: "Ed448Point") -> "Ed448Point":
        """Point subtraction: P - Q = P + (-Q)."""
        return self + (-other)

    def double(self) -> "Ed448Point":
        """Dedicated Point Doubling on Ed448 (RFC 8032)."""
        B = ((self.X + self.Y) * (self.X + self.Y)) % P_ED448
        C = (self.X * self.X) % P_ED448
        D = (self.Y * self.Y) % P_ED448
        E = (C + D) % P_ED448
        H = (self.Z * self.Z) % P_ED448
        J = (E - 2 * H) % P_ED448
        X3 = ((B - E) * J) % P_ED448
        Y3 = (E * (C - D)) % P_ED448
        Z3 = (E * J) % P_ED448
        T3 = ((B - E) * (C - D)) % P_ED448
        return Ed448Point(X3, Y3, Z3, T3)

    def __rmul__(self, scalar: int) -> "Ed448Point":
        """Scalar Point Multiplication k * P (PM) using double-and-add."""
        k = scalar % Q_ED448
        if k == 0 or self.is_infinity():
            return Ed448Point.infinity()
        result = Ed448Point.infinity()
        addend = self
        while k > 0:
            if k & 1:
                result = result + addend
            addend = addend.double()
            k >>= 1
        return result

    def __mul__(self, scalar: int) -> "Ed448Point":
        return self.__rmul__(scalar)

    def to_bytes(self) -> bytes:
        """Canonical 112-byte serialization of affine coordinates (x, y)."""
        x, y = self.to_affine()
        return x.to_bytes(SCALAR_BYTES, "little") + y.to_bytes(SCALAR_BYTES, "little")


# Generator G of the prime-order subgroup E = <G>
G_BASE = Ed448Point(GX_ED448, GY_ED448)
O_INF = Ed448Point.infinity()


# =============================================================================
# 2. UNIFORM SAMPLING, CANONICAL ENCODING, AND SHAKE256 HASH / KDF FUNCTIONS
# =============================================================================
def sample_zq() -> int:
    """Uniformly sample a scalar from Z_q = {0, 1, ..., q-1}."""
    return secrets.randbelow(Q_ED448)


def sample_zq_star() -> int:
    """Uniformly sample a non-zero scalar from Z_q^* = {1, 2, ..., q-1}."""
    return 1 + secrets.randbelow(Q_ED448 - 1)


def encode_scalar(val: int) -> bytes:
    """Encode(z): Canonical representation of an element in Z_q as a 56-byte string."""
    return (val % Q_ED448).to_bytes(SCALAR_BYTES, "little")


def decode_scalar(data: bytes) -> int:
    """Decode(bytes): Recover a scalar element in Z_q from a 56-byte string."""
    if len(data) != SCALAR_BYTES:
        raise ValueError(f"Expected {SCALAR_BYTES}-byte encoding.")
    return int.from_bytes(data, "little")


def xor_bytes(a: bytes, b: bytes) -> bytes:
    """Byte-wise XOR of two equal-length byte strings."""
    return bytes(x ^ y for x, y in zip(a, b))


def _serialize_arg(arg: object) -> bytes:
    """Length-prefixed unambiguous byte serialization for hash/KDF inputs."""
    if isinstance(arg, bytes):
        raw = arg
    elif isinstance(arg, str):
        raw = arg.encode("utf-8")
    elif isinstance(arg, int):
        raw = encode_scalar(arg)
    elif isinstance(arg, Ed448Point):
        raw = arg.to_bytes()
    elif isinstance(arg, tuple):
        raw = b"".join(_serialize_arg(x) for x in arg)
    else:
        raise TypeError(f"Unsupported argument type: {type(arg)}")
    return len(raw).to_bytes(4, "little") + raw


def shake256_hash_to_zq(domain_tag: bytes, *args: object) -> int:
    """
    Domain-separated hash function mapping {0,1}^* -> Z_q instantiated from
    SHAKE256 by extracting 112 bytes (896 bits) and reducing modulo q.
    """
    shake = hashlib.shake_256()
    shake.update(_serialize_arg(domain_tag))
    for arg in args:
        shake.update(_serialize_arg(arg))
    digest_112 = shake.digest(HASH_EXTRACT_BYTES)
    return int.from_bytes(digest_112, "little") % Q_ED448


# Domain-separated hash functions defined in Section 4.2 of the paper
def H_1(Y_C: Ed448Point, M: bytes, K: Ed448Point) -> int:
    return shake256_hash_to_zq(b"ENTERPRISE_EVOTING_H1", Y_C, M, K)


def H_2(K: Ed448Point, K_1: Ed448Point, K_2: Ed448Point) -> int:
    return shake256_hash_to_zq(b"ENTERPRISE_EVOTING_H2", K, K_1, K_2)


def H_3(h_2: int, W: Ed448Point) -> int:
    return shake256_hash_to_zq(b"ENTERPRISE_EVOTING_H3", h_2, W)


def H_A1(
    ID_V: str,
    Y_V: Ed448Point,
    Y_C: Ed448Point,
    sid: bytes,
    ts: int,
    C_1: Tuple[Ed448Point, Ed448Point],
    A_1: Ed448Point,
) -> int:
    return shake256_hash_to_zq(
        b"ENTERPRISE_EVOTING_HA1", ID_V, Y_V, Y_C, sid, ts, C_1, A_1
    )


def H_A2(
    ID_V: str,
    Y_V: Ed448Point,
    Y_C: Ed448Point,
    sid: bytes,
    ts: int,
    C_1: Tuple[Ed448Point, Ed448Point],
    C_2: Tuple[Ed448Point, Ed448Point],
    tilde_h_3: int,
    A_2: Ed448Point,
) -> int:
    return shake256_hash_to_zq(
        b"ENTERPRISE_EVOTING_HA2", ID_V, Y_V, Y_C, sid, ts, C_1, C_2, tilde_h_3, A_2
    )


def KDF_Mask(
    U_1: Ed448Point,
    U_2: Ed448Point,
    sid: bytes,
    C_1: Tuple[Ed448Point, Ed448Point],
    C_2: Tuple[Ed448Point, Ed448Point],
    tilde_h_3: int,
    length: int = SCALAR_BYTES,
) -> bytes:
    """
    Keystream mask derivation function KDF(MSK, U_1, U_2, sid, C_1, C_2, tilde_h_3; n)
    producing a 56-byte mask derived from the shared secret points (U_1, U_2).
    """
    shake = hashlib.shake_256()
    shake.update(_serialize_arg(b"MSK"))
    for item in (U_1, U_2, sid, C_1, C_2, tilde_h_3):
        shake.update(_serialize_arg(item))
    return shake.digest(length)


# =============================================================================
# 3. PROTOCOL MESSAGE AND BALLOT SIGNATURE DATA STRUCTURES
# =============================================================================
@dataclass
class Pass1Message:
    """Pass 1 message sent from Voter/Shareholder (V) to Signing Committee Server (S)."""
    ID_V: str
    sid: bytes
    ts: int
    C_1: Tuple[Ed448Point, Ed448Point]
    A_1: Ed448Point
    zeta_1: int


@dataclass
class Pass2Message:
    """Pass 2 message sent from Signing Committee Server (S) to Voter/Shareholder (V)."""
    sid: bytes
    C_2: Tuple[Ed448Point, Ed448Point]


@dataclass
class Pass3Message:
    """Pass 3 message sent from Voter/Shareholder (V) to Signing Committee Server (S)."""
    sid: bytes
    tilde_h_3: int
    A_2: Ed448Point
    zeta_2: int


@dataclass
class Pass4Message:
    """Pass 4 message sent from Signing Committee Server (S) to Voter/Shareholder (V)."""
    sid: bytes
    C_3: bytes


@dataclass
class BallotSignature:
    """Public unblinded ballot signature sigma = (W, K, z)."""
    W: Ed448Point
    K: Ed448Point
    z: int


# =============================================================================
# 4. ARCHITECTURAL ENTITIES OF THE ENTERPRISE E-VOTING SYSTEM (SECTION 4)
# =============================================================================
class EnterpriseIAM:
    """
    1. Enterprise Identity and Access Management & PKI (Enterprise IAM & PKI):
       Verifies shareholder/employee eligibility, maintains the public identity
       key directory (ID_V, Y_V), and certifies the Committee's public key Y_C.
    """
    def __init__(self):
        self.voter_directory: Dict[str, Ed448Point] = {}
        self.committee_id: str = "COMMITTEE_SERVER_01"
        self.Y_C: Optional[Ed448Point] = None

    def register_committee(self, Y_C: Ed448Point) -> None:
        if Y_C.is_infinity() or not Y_C.is_on_curve():
            raise ValueError("Invalid Signing Committee public key Y_C.")
        self.Y_C = Y_C

    def register_voter(self, ID_V: str, Y_V: Ed448Point) -> None:
        """Verify Y_V in E - {O} via IAM and store profile (ID_V, Y_V) in directory."""
        if Y_V.is_infinity() or not Y_V.is_on_curve():
            raise ValueError(f"Invalid public key Y_V for member {ID_V}.")
        self.voter_directory[ID_V] = Y_V

    def get_voter_pubkey(self, ID_V: str) -> Ed448Point:
        if ID_V not in self.voter_directory:
            raise PermissionError(f"Identity {ID_V} is not registered in Enterprise IAM.")
        return self.voter_directory[ID_V]


class SigningCommitteeServer:
    """
    3. Signing Committee Server (S):
       - Holds signing key pair (d_C, Y_C = d_C G).
       - Maintains the identity-randomness state table T = {(ID_V, r_2)} to prevent
         secret nonce reuse and double-voting.
       - Operates an Atomic Sequential Session Queue (l_conc = 1) to eliminate
         concurrent polynomial ROS attacks (Benhamouda et al., 2021; Harding & Xu, 2024).
    """
    def __init__(self, iam: EnterpriseIAM, session_timeout_sec: float = 0.5):
        self.iam = iam
        self.d_C: int = sample_zq_star()
        self.Y_C: Ed448Point = self.d_C * G_BASE
        self.iam.register_committee(self.Y_C)

        # Initialize empty state table T = \emptyset storing (ID_V -> r_2)
        # and an O(1) lookup set for all previously generated nonces r_2
        self.state_table_T: Dict[str, int] = {}
        self.used_r2_values: set[int] = set()
        self.completed_voters: set[str] = set()

        # Atomic Sequential Session Queue: at most l_conc = 1 active session
        # is permitted between Pass 2 and Pass 4 at any given time
        self.active_session: Optional[Dict[str, object]] = None
        self.session_timeout_sec = session_timeout_sec

    def _cleanup_expired_session(self) -> None:
        """Abort pending session if it exceeds the short 500 ms timeout threshold."""
        if self.active_session is not None:
            elapsed = time.perf_counter() - float(self.active_session["created_at"])
            if elapsed > self.session_timeout_sec:
                self.active_session = None

    def blind_sign_pass2(self, msg1: Pass1Message) -> Pass2Message:
        """
        Pass 2 (BlindSign_1):
        - Check ts, sid, and voting eligibility (ID_V not in T).
        - Verify first EC-NIPoK proof: zeta_1 G == A_1 - c_1 Y_V.
        - Decrypt initial commitment: U_1 = E_{1,2} - d_C E_{1,1}.
        - Sample r_2 in Z_q^*; check state table T: if r_2 in T, resample r_2 until
          unique; if r_2 not in T, insert (ID_V, r_2) into T.
        - Encrypt server contribution U_2 = r_2 G under Y_V as C_2 = (E_{2,1}, E_{2,2}).
        """
        self._cleanup_expired_session()

        # Enforce Atomic Sequential Session Queue (l_conc = 1)
        if self.active_session is not None:
            raise RuntimeError(
                "Atomic Sequential Session Queue is busy: only 1 active session is permitted."
            )

        # Check voting eligibility (ID_V not in T)
        if msg1.ID_V in self.state_table_T or msg1.ID_V in self.completed_voters:
            raise PermissionError(
                f"Rejected: Member {msg1.ID_V} already exists in state table T (Double-voting prevented)."
            )

        Y_V = self.iam.get_voter_pubkey(msg1.ID_V)
        E_11, E_12 = msg1.C_1
        if (
            msg1.A_1.is_infinity()
            or not msg1.A_1.is_on_curve()
            or not E_11.is_on_curve()
            or not E_12.is_on_curve()
        ):
            raise ValueError("Invalid curve point in Pass 1 message.")

        # Verify first EC-NIPoK proof of secret key knowledge
        c_1 = H_A1(msg1.ID_V, Y_V, self.Y_C, msg1.sid, msg1.ts, msg1.C_1, msg1.A_1)
        lhs = msg1.zeta_1 * G_BASE
        rhs = msg1.A_1 - (c_1 * Y_V)
        if lhs != rhs:
            raise PermissionError("Pass 1 EC-NIPoK authentication failed!")

        # Decrypt voter's initial point U_1 = E_{1,2} - d_C E_{1,1}
        U_1 = E_12 - (self.d_C * E_11)

        # Sample secret nonce r_2 in Z_q^* and enforce uniqueness against table T
        while True:
            r_2 = sample_zq_star()
            if r_2 not in self.used_r2_values:
                break

        # Record pair (ID_V, r_2) in state table T
        self.state_table_T[msg1.ID_V] = r_2
        self.used_r2_values.add(r_2)

        # Sample tau_2 in Z_q^*, compute U_2 = r_2 G, and encrypt under Y_V
        tau_2 = sample_zq_star()
        U_2 = r_2 * G_BASE
        E_21 = tau_2 * G_BASE
        E_22 = U_2 + (tau_2 * Y_V)
        C_2 = (E_21, E_22)

        # Store pending atomic session state
        self.active_session = {
            "ID_V": msg1.ID_V,
            "Y_V": Y_V,
            "sid": msg1.sid,
            "ts": msg1.ts,
            "C_1": msg1.C_1,
            "C_2": C_2,
            "U_1": U_1,
            "U_2": U_2,
            "created_at": time.perf_counter(),
        }
        return Pass2Message(sid=msg1.sid, C_2=C_2)

    def blind_sign_pass4(self, msg3: Pass3Message) -> Pass4Message:
        """
        Pass 4 (BlindSign_2):
        - Match session sid and verify expiration window.
        - Verify second EC-NIPoK proof: zeta_2 G == A_2 - c_2 Y_V.
        - Retrieve (ID_V, r_2) from table T and compute response:
          z_1 = (r_2 + tilde_h_3 d_C) mod q.
        - Derive 56-byte mask kappa and compute C_3 = kappa XOR Encode(z_1).
        - Atomically close session and permanently lock voting status for ID_V.
        """
        self._cleanup_expired_session()
        if self.active_session is None or self.active_session["sid"] != msg3.sid:
            raise RuntimeError("Blind signing session does not exist or has expired.")

        ID_V = str(self.active_session["ID_V"])
        Y_V: Ed448Point = self.active_session["Y_V"]  # type: ignore
        ts = int(self.active_session["ts"])  # type: ignore
        C_1: Tuple[Ed448Point, Ed448Point] = self.active_session["C_1"]  # type: ignore
        C_2: Tuple[Ed448Point, Ed448Point] = self.active_session["C_2"]  # type: ignore
        U_1: Ed448Point = self.active_session["U_1"]  # type: ignore
        U_2: Ed448Point = self.active_session["U_2"]  # type: ignore

        if msg3.A_2.is_infinity() or not msg3.A_2.is_on_curve():
            self.active_session = None
            raise ValueError("Invalid commitment point A_2 in Pass 3.")

        # Verify second EC-NIPoK proof
        c_2 = H_A2(ID_V, Y_V, self.Y_C, msg3.sid, ts, C_1, C_2, msg3.tilde_h_3, msg3.A_2)
        lhs = msg3.zeta_2 * G_BASE
        rhs = msg3.A_2 - (c_2 * Y_V)
        if lhs != rhs:
            self.active_session = None
            raise PermissionError("Pass 3 EC-NIPoK authentication failed!")

        # Retrieve (ID_V, r_2) from state table T and compute blind response z_1
        r_2 = self.state_table_T[ID_V]
        z_1 = (r_2 + msg3.tilde_h_3 * self.d_C) % Q_ED448

        # Derive 56-byte mask kappa and compute C_3 = kappa XOR Encode(z_1)
        kappa = KDF_Mask(U_1, U_2, msg3.sid, C_1, C_2, msg3.tilde_h_3, SCALAR_BYTES)
        C_3 = xor_bytes(kappa, encode_scalar(z_1))

        # Atomically close session for ID_V
        self.completed_voters.add(ID_V)
        self.active_session = None

        return Pass4Message(sid=msg3.sid, C_3=C_3)


class EnterpriseVoter:
    """
    2. Voting Member / Shareholder (Voter - V):
       Registers identity key pair (d_V, Y_V), initiates Pass 1 (Blind_1),
       performs dual-base blinding (u, w) in Pass 3 (Blind_2), and unblinds (Unblind).
    """
    def __init__(self, ID_V: str, iam: EnterpriseIAM):
        self.ID_V = ID_V
        self.d_V: int = sample_zq_star()
        self.Y_V: Ed448Point = self.d_V * G_BASE
        iam.register_voter(self.ID_V, self.Y_V)
        self.Y_C: Ed448Point = iam.Y_C  # type: ignore

        # Local ephemeral state maintained by the voter during a signing session
        self._state: Dict[str, object] = {}

    def blind_pass1(self) -> Pass1Message:
        """
        Pass 1 (Blind_1):
        - Sample r_1 in Z_q and tau_1, eta_1 in Z_q^* (independent of ballot M).
        - Compute U_1 = r_1 G, A_1 = eta_1 G, C_1 = (tau_1 G, U_1 + tau_1 Y_C).
        - Compute first EC-NIPoK proof: c_1, zeta_1 = (eta_1 - c_1 d_V) mod q.
        """
        r_1 = sample_zq()
        tau_1 = sample_zq_star()
        eta_1 = sample_zq_star()

        U_1 = r_1 * G_BASE
        A_1 = eta_1 * G_BASE
        E_11 = tau_1 * G_BASE
        E_12 = U_1 + (tau_1 * self.Y_C)
        C_1 = (E_11, E_12)

        sid = secrets.token_bytes(32)  # 256-bit session identifier
        ts = int(time.time())

        c_1 = H_A1(self.ID_V, self.Y_V, self.Y_C, sid, ts, C_1, A_1)
        zeta_1 = (eta_1 - c_1 * self.d_V) % Q_ED448

        self._state = {
            "sid": sid,
            "ts": ts,
            "r_1": r_1,
            "U_1": U_1,
            "C_1": C_1,
        }
        return Pass1Message(
            ID_V=self.ID_V, sid=sid, ts=ts, C_1=C_1, A_1=A_1, zeta_1=zeta_1
        )

    def blind_pass3(self, msg2: Pass2Message, ballot_message: bytes) -> Pass3Message:
        """
        Pass 3 (Blind_2):
        - Decrypt U_2 = E_{2,2} - d_V E_{2,1}.
        - Freshly sample independent, uniformly distributed scalars u, w, gamma in Z_q.
        - Dual-base commitment re-randomization: W = U_1 + U_2 + u G + w Y_C.
        - Compute K = gamma G, h_1, K_1, K_2, h_2, h_3, and blind challenge
          tilde_h_3 = (h_3 + w) mod q.
        - Generate second EC-NIPoK proof: (A_2, zeta_2).
        """
        if msg2.sid != self._state.get("sid"):
            raise ValueError("Session identifier mismatch in Pass 2.")

        E_21, E_22 = msg2.C_2
        U_2 = E_22 - (self.d_V * E_21)
        if not U_2.is_on_curve():
            raise ValueError("Decrypted server contribution U_2 is not on Ed448 curve.")

        # Uniformly sample independent blinding scalars (u, w, gamma) in Z_q^3
        u = sample_zq()
        w = sample_zq()
        gamma = sample_zq()

        U_1: Ed448Point = self._state["U_1"]  # type: ignore

        # Dual-base re-randomization: W = U_1 + U_2 + u G + w Y_C
        W = U_1 + U_2 + (u * G_BASE) + (w * self.Y_C)

        # Ballot-anchored hash chain for M
        K = gamma * G_BASE
        h_1 = H_1(self.Y_C, ballot_message, K)
        K_1 = h_1 * G_BASE
        K_2 = K + K_1
        h_2 = H_2(K, K_1, K_2)
        h_3 = H_3(h_2, W)

        # Blind the signing challenge: tilde_h_3 = (h_3 + w) mod q
        tilde_h_3 = (h_3 + w) % Q_ED448

        # Generate second EC-NIPoK proof
        eta_2 = sample_zq_star()
        A_2 = eta_2 * G_BASE
        sid: bytes = self._state["sid"]  # type: ignore
        ts: int = self._state["ts"]  # type: ignore
        C_1: Tuple[Ed448Point, Ed448Point] = self._state["C_1"]  # type: ignore

        c_2 = H_A2(
            self.ID_V, self.Y_V, self.Y_C, sid, ts, C_1, msg2.C_2, tilde_h_3, A_2
        )
        zeta_2 = (eta_2 - c_2 * self.d_V) % Q_ED448

        # Store local state for the Unblind phase
        self._state.update(
            {
                "C_2": msg2.C_2,
                "U_2": U_2,
                "u": u,
                "w": w,
                "W": W,
                "K": K,
                "tilde_h_3": tilde_h_3,
                "M": ballot_message,
            }
        )
        return Pass3Message(sid=sid, tilde_h_3=tilde_h_3, A_2=A_2, zeta_2=zeta_2)

    def unblind(self, msg4: Pass4Message) -> BallotSignature:
        """
        Unblinding at Shareholder Device (Unblind):
        - Re-derive mask kappa and decode z_1 = Decode(kappa XOR C_3).
        - Verify algebraic validity: z_1 G == U_2 + tilde_h_3 Y_C.
        - Accumulate blinding scalars: z = (z_1 + r_1 + u) mod q.
        - Output public ballot signature sigma = (W, K, z).
        """
        sid: bytes = self._state["sid"]  # type: ignore
        if msg4.sid != sid:
            raise ValueError("Session identifier mismatch in Pass 4.")

        U_1: Ed448Point = self._state["U_1"]  # type: ignore
        U_2: Ed448Point = self._state["U_2"]  # type: ignore
        C_1: Tuple[Ed448Point, Ed448Point] = self._state["C_1"]  # type: ignore
        C_2: Tuple[Ed448Point, Ed448Point] = self._state["C_2"]  # type: ignore
        tilde_h_3: int = self._state["tilde_h_3"]  # type: ignore
        r_1: int = self._state["r_1"]  # type: ignore
        u: int = self._state["u"]  # type: ignore
        W: Ed448Point = self._state["W"]  # type: ignore
        K: Ed448Point = self._state["K"]  # type: ignore

        kappa = KDF_Mask(U_1, U_2, sid, C_1, C_2, tilde_h_3, SCALAR_BYTES)
        z_1 = decode_scalar(xor_bytes(kappa, msg4.C_3))

        # Verify algebraic validity of the Committee's blind response
        if (z_1 * G_BASE) != (U_2 + (tilde_h_3 * self.Y_C)):
            raise ValueError("Invalid blind signing response z_1 from Committee Server!")

        # Remove blinding factors
        z = (z_1 + r_1 + u) % Q_ED448
        return BallotSignature(W=W, K=K, z=z)


class TallyingServer:
    """
    4. Tallying Server and Public Bulletin Board (Tallying Server - T):
       Receives anonymous ballot packages (M, W, K, z) and performs public verification.
    """
    def __init__(self, Y_C: Ed448Point):
        self.Y_C = Y_C
        self.bulletin_board = []

    def verify_and_record(self, ballot_message: bytes, sigma: BallotSignature) -> bool:
        """
        Stage 3 (Verify):
        Check W, K in E and z in Z_q; recompute h_1, K_1, K_2, h_2, h_3
        and accept the ballot if and only if: z G == W + h_3 Y_C.
        """
        if not sigma.W.is_on_curve() or not sigma.K.is_on_curve():
            return False
        if not (0 <= sigma.z < Q_ED448):
            return False

        h_1 = H_1(self.Y_C, ballot_message, sigma.K)
        K_1 = h_1 * G_BASE
        K_2 = sigma.K + K_1
        h_2 = H_2(sigma.K, K_1, K_2)
        h_3 = H_3(h_2, sigma.W)

        lhs = sigma.z * G_BASE
        rhs = sigma.W + (h_3 * self.Y_C)
        is_valid = lhs == rhs
        if is_valid:
            self.bulletin_board.append((ballot_message, sigma))
        return is_valid


# =============================================================================
# 5. MATHEMATICAL VERIFICATION OF PERFECT BLINDNESS (THEOREM 2) & BENCHMARKING
# =============================================================================
def verify_perfect_blindness_theorem(
    voter0: EnterpriseVoter,
    voter1: EnterpriseVoter,
    sig0: BallotSignature,
    sig1: BallotSignature,
    M0: bytes,
    M1: bytes,
    Y_C: Ed448Point,
) -> bool:
    """
    Experimental verification of Theorem 2 (Information-Theoretic Perfect Blindness):
    For any two successful signing sessions i in {0, 1} and any two valid public
    ballots j in {0, 1}, there exists a unique blinding pair (u_{i,j}, w_{i,j}) in Z_q^2
    that maps session transcript i to public ballot j on the elliptic curve E.
    """
    sessions = [voter0._state, voter1._state]
    ballots = [(M0, sig0), (M1, sig1)]

    for i, sess in enumerate(sessions):
        U_1i: Ed448Point = sess["U_1"]  # type: ignore
        U_2i: Ed448Point = sess["U_2"]  # type: ignore
        r_1i: int = sess["r_1"]  # type: ignore
        tilde_h_3i: int = sess["tilde_h_3"]  # type: ignore
        u_actual: int = sess["u"]  # type: ignore
        sig_actual = sig0 if i == 0 else sig1
        z_1i = (sig_actual.z - r_1i - u_actual) % Q_ED448

        for j, (Mj, sigj) in enumerate(ballots):
            h_1j = H_1(Y_C, Mj, sigj.K)
            K_1j = h_1j * G_BASE
            K_2j = sigj.K + K_1j
            h_2j = H_2(sigj.K, K_1j, K_2j)
            h_3j = H_3(h_2j, sigj.W)

            # Bijective mapping from Theorem 2:
            w_ij = (tilde_h_3i - h_3j) % Q_ED448
            u_ij = (sigj.z - z_1i - r_1i) % Q_ED448

            # Verify group equation: U_{1,i} + U_{2,i} + u_{i,j} G + w_{i,j} Y_C == W_j
            reconstructed_W = U_1i + U_2i + (u_ij * G_BASE) + (w_ij * Y_C)
            if reconstructed_W != sigj.W:
                return False
    return True


def run_demonstration_and_benchmark(iterations: int = 10) -> None:
    print("=" * 78)
    print("ENTERPRISE E-VOTING PROTOCOL SIMULATION AND BENCHMARK ON ED448 (CURVE448)")
    print("=" * 78)

    # 1. Initialize architecture and verify Correctness (Theorem 1)
    iam = EnterpriseIAM()
    committee = SigningCommitteeServer(iam)
    tally = TallyingServer(committee.Y_C)

    voter_a = EnterpriseVoter("SHAREHOLDER_001_ALICE", iam)
    voter_b = EnterpriseVoter("SHAREHOLDER_002_BOB", iam)

    ballot_a = b"APPROVE: Resolution on 2026 Annual Dividend Distribution"
    ballot_b = b"REJECT: Proposal on Additional Equity Issuance"

    # 4-pass interactive voting session for Shareholder A
    m1_a = voter_a.blind_pass1()
    m2_a = committee.blind_sign_pass2(m1_a)
    m3_a = voter_a.blind_pass3(m2_a, ballot_a)
    m4_a = committee.blind_sign_pass4(m3_a)
    sig_a = voter_a.unblind(m4_a)
    valid_a = tally.verify_and_record(ballot_a, sig_a)

    # 4-pass interactive voting session for Shareholder B
    m1_b = voter_b.blind_pass1()
    m2_b = committee.blind_sign_pass2(m1_b)
    m3_b = voter_b.blind_pass3(m2_b, ballot_b)
    m4_b = committee.blind_sign_pass4(m3_b)
    sig_b = voter_b.unblind(m4_b)
    valid_b = tally.verify_and_record(ballot_b, sig_b)

    print(f"[1] Theorem 1 Verification (Correctness):")
    print(f"    - Ballot from {voter_a.ID_V}: Valid = {valid_a}")
    print(f"    - Ballot from {voter_b.ID_V}: Valid = {valid_b}")
    print(f"    - Recorded (ID_V, r_2) entries in state table T: {len(committee.state_table_T)}")

    # 2. Verify Theorem 2 (Information-Theoretic Perfect Blindness Adv^blind = 0)
    blindness_ok = verify_perfect_blindness_theorem(
        voter_a, voter_b, sig_a, sig_b, ballot_a, ballot_b, committee.Y_C
    )
    print(f"[2] Theorem 2 Verification (Perfect Blindness Adv^blind = 0):")
    print(f"    - Unique bijection (u_{{i,j}}, w_{{i,j}}) exists for both b=0 and b=1: {blindness_ok}")

    # 3. Verify Theorem 4 (State Table T Double-Voting & Atomic Queue ROS Protection)
    double_vote_blocked = False
    try:
        committee.blind_sign_pass2(voter_a.blind_pass1())
    except PermissionError:
        double_vote_blocked = True

    voter_c = EnterpriseVoter("SHAREHOLDER_003_CHARLIE", iam)
    voter_d = EnterpriseVoter("SHAREHOLDER_004_DAVID", iam)
    _ = committee.blind_sign_pass2(voter_c.blind_pass1())
    concurrent_ros_blocked = False
    try:
        # Attempt to open a parallel session while SHAREHOLDER_003 session is still open
        committee.blind_sign_pass2(voter_d.blind_pass1())
    except RuntimeError:
        concurrent_ros_blocked = True

    print(f"[3] Theorem 4 Verification (State Table T & Atomic Sequential Queue):")
    print(f"    - Double-voting request blocked via state table T: {double_vote_blocked}")
    print(f"    - Concurrent session blocked (Polynomial ROS attack prevented): {concurrent_ros_blocked}")

    # 4. Benchmark average execution time across protocol phases (Table 3)
    t_keygen, t_blind, t_blindsign, t_unblind, t_verify = 0.0, 0.0, 0.0, 0.0, 0.0
    bench_iam = EnterpriseIAM()
    bench_server = SigningCommitteeServer(bench_iam)
    bench_tally = TallyingServer(bench_server.Y_C)

    for idx in range(iterations):
        vid = f"BENCH_VOTER_{idx}"
        # Measure KeyGen (2 PM: Committee key + Voter key)
        t0 = time.perf_counter()
        _d_tmp = sample_zq_star()
        _ = _d_tmp * G_BASE
        voter = EnterpriseVoter(vid, bench_iam)
        t1 = time.perf_counter()
        t_keygen += (t1 - t0) * 1000.0

        msg_payload = f"Enterprise AGM Resolution Ballot #{idx}".encode("utf-8")

        # Pass 1 (Blind_1)
        t0 = time.perf_counter()
        p1 = voter.blind_pass1()
        t1 = time.perf_counter()
        t_blind += (t1 - t0) * 1000.0

        # Pass 2 (BlindSign_1)
        t0 = time.perf_counter()
        p2 = bench_server.blind_sign_pass2(p1)
        t1 = time.perf_counter()
        t_blindsign += (t1 - t0) * 1000.0

        # Pass 3 (Blind_2)
        t0 = time.perf_counter()
        p3 = voter.blind_pass3(p2, msg_payload)
        t1 = time.perf_counter()
        t_blind += (t1 - t0) * 1000.0

        # Pass 4 (BlindSign_2)
        t0 = time.perf_counter()
        p4 = bench_server.blind_sign_pass4(p3)
        t1 = time.perf_counter()
        t_blindsign += (t1 - t0) * 1000.0

        # Unblind
        t0 = time.perf_counter()
        sig = voter.unblind(p4)
        t1 = time.perf_counter()
        t_unblind += (t1 - t0) * 1000.0

        # Verify
        t0 = time.perf_counter()
        assert bench_tally.verify_and_record(msg_payload, sig)
        t1 = time.perf_counter()
        t_verify += (t1 - t0) * 1000.0

    k_avg = t_keygen / iterations
    b_avg = t_blind / iterations
    bs_avg = t_blindsign / iterations
    u_avg = t_unblind / iterations
    v_avg = t_verify / iterations
    total_avg = k_avg + b_avg + bs_avg + u_avg + v_avg

    print("-" * 78)
    print(f"[4] AVERAGE EXECUTION TIME BENCHMARK ({iterations} RUNS - UNIT: ms):")
    print(f"    - KeyGen (2 PM)                     : {k_avg:8.2f} ms")
    print(f"    - Blind (Blind_1 + Blind_2 - 10 PM) : {b_avg:8.2f} ms")
    print(f"    - BlindSign (Pass 2 + Pass 4 - 8 PM): {bs_avg:8.2f} ms")
    print(f"    - Unblind (2 PM)                    : {u_avg:8.2f} ms")
    print(f"    - Verify (3 PM)                     : {v_avg:8.2f} ms")
    print(f"    => TOTAL END-TO-END EXECUTION TIME  : {total_avg:8.2f} ms")
    print("=" * 78)


if __name__ == "__main__":
    run_demonstration_and_benchmark(iterations=10)
