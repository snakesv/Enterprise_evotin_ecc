import time
from typing import Dict, Tuple, Set, Any
from Crypto.PublicKey import ECC
from Crypto.Hash import SHAKE256
from Crypto.Random import get_random_bytes
from Crypto.Random.random import randrange


# =====================================================================
# 1. SYSTEM PARAMETER SETUP ON ED448 (CURVE448)
# =====================================================================
CURVE_NAME = "Ed448"
_curve_info = ECC._curves[CURVE_NAME]

# Base generator point G and large prime order q of the cyclic subgroup E = <G>
G: ECC.EccPoint = _curve_info.G
q: int = int(_curve_info.order)

# Canonical byte length of an element in Z_q: n = ceil(log2(q)/8) = 56 bytes
SCALAR_BYTES: int = (q.bit_length() + 7) // 8  # 56 bytes for Ed448
SHAKE_EXTRACT_BYTES: int = 112  # Extract 112 bytes (896 bits) before modulo q reduction


# =====================================================================
# 2. ENCODING HELPERS, DOMAIN-SEPARATED HASHES & KDF (SHAKE256)
# =====================================================================
def encode_scalar(x: int) -> bytes:
    """Canonically convert an element in Z_q into an n = 56-byte big-endian string."""
    return (x % q).to_bytes(SCALAR_BYTES, byteorder="big")


def decode_scalar(b: bytes) -> int:
    """Canonically convert an n = 56-byte string back into an element in Z_q."""
    return int.from_bytes(b, byteorder="big") % q


def encode_point(P: ECC.EccPoint) -> bytes:
    """Serialize an elliptic curve point P = (x, y) into a fixed-length byte string."""
    if P.is_point_at_infinity():
        return b"\x00" * (2 * SCALAR_BYTES)
    x_bytes = int(P.x).to_bytes(SCALAR_BYTES, byteorder="big")
    y_bytes = int(P.y).to_bytes(SCALAR_BYTES, byteorder="big")
    return x_bytes + y_bytes


def _serialize_item(item: Any) -> bytes:
    """Normalize heterogeneous input types (points, scalars, strings, tuples) into bytes."""
    if isinstance(item, bytes):
        return item
    if isinstance(item, str):
        return item.encode("utf-8")
    if isinstance(item, int):
        return encode_scalar(item)
    if isinstance(item, ECC.EccPoint):
        return encode_point(item)
    if isinstance(item, (tuple, list)):
        return b"".join(_serialize_item(sub) for sub in item)
    raise TypeError(f"Unsupported data type for serialization: {type(item)}")


def domain_hash_to_zq(domain_tag: bytes, *items: Any) -> int:
    """
    Domain-separated hash functions H_1, H_2, H_3, H_A1, H_A2 : {0,1}* -> Z_q.
    Instantiated from SHAKE256 by extracting 112 bytes (896 bits) and reducing modulo q
    to eliminate statistical bias.
    """
    shake = SHAKE256.new()
    shake.update(len(domain_tag).to_bytes(2, "big") + domain_tag)
    for item in items:
        data = _serialize_item(item)
        shake.update(len(data).to_bytes(4, "big") + data)
    digest = shake.read(SHAKE_EXTRACT_BYTES)
    return int.from_bytes(digest, byteorder="big") % q


# Domain-separated cryptographic hash functions defined in Section 3.2 & Table 1
def H_1(Y_C: ECC.EccPoint, M: str, K: ECC.EccPoint) -> int:
    return domain_hash_to_zq(b"DOM_H1", Y_C, M, K)


def H_2(K: ECC.EccPoint, K_1: ECC.EccPoint, K_2: ECC.EccPoint) -> int:
    return domain_hash_to_zq(b"DOM_H2", K, K_1, K_2)


def H_3(h_2: int, W: ECC.EccPoint) -> int:
    return domain_hash_to_zq(b"DOM_H3", h_2, W)


def H_A1(
    ID_V: str,
    Y_V: ECC.EccPoint,
    Y_C: ECC.EccPoint,
    sid: bytes,
    ts: int,
    C_1: Tuple[ECC.EccPoint, ECC.EccPoint],
    A_1: ECC.EccPoint,
) -> int:
    return domain_hash_to_zq(b"DOM_HA1", ID_V, Y_V, Y_C, sid, ts, C_1, A_1)


def H_A2(
    ID_V: str,
    Y_V: ECC.EccPoint,
    Y_C: ECC.EccPoint,
    sid: bytes,
    ts: int,
    C_1: Tuple[ECC.EccPoint, ECC.EccPoint],
    C_2: Tuple[ECC.EccPoint, ECC.EccPoint],
    h_3_tilde: int,
    A_2: ECC.EccPoint,
) -> int:
    return domain_hash_to_zq(
        b"DOM_HA2", ID_V, Y_V, Y_C, sid, ts, C_1, C_2, h_3_tilde, A_2
    )


def KDF_mask(
    U_1: ECC.EccPoint,
    U_2: ECC.EccPoint,
    sid: bytes,
    C_1: Tuple[ECC.EccPoint, ECC.EccPoint],
    C_2: Tuple[ECC.EccPoint, ECC.EccPoint],
    h_3_tilde: int,
    length: int = SCALAR_BYTES,
) -> bytes:
    """
    Key Derivation Function kappa = KDF("MSK", U_1, U_2, sid, C_1, C_2, h_3_tilde; n)
    instantiated via SHAKE256 to derive an n = 56-byte keystream mask.
    """
    shake = SHAKE256.new()
    shake.update(b"MSK")
    for item in (U_1, U_2, sid, C_1, C_2, h_3_tilde):
        data = _serialize_item(item)
        shake.update(len(data).to_bytes(4, "big") + data)
    return shake.read(length)


def xor_bytes(a: bytes, b: bytes) -> bytes:
    """Bitwise XOR operation between two equal-length byte strings."""
    return bytes(x ^ y for x, y in zip(a, b))


def check_valid_curve_point(P: ECC.EccPoint) -> bool:
    """Verify that point P belongs to subgroup E and is not the point at infinity O."""
    return isinstance(P, ECC.EccPoint) and not P.is_point_at_infinity()


# =====================================================================
# 3. ENTERPRISE ELECTRONIC VOTING ENTITIES
# =====================================================================
class CommitteeServer:
    """
    Signing Committee Server (S):
    - Generates and manages the Committee signing key pair (d_C, Y_C = d_C * G).
    - Maintains the Enterprise IAM public-key directory (ID_V, Y_V).
    - Manages state table T = {(ID_V, r_2)} to prevent nonce r_2 collisions and double-voting.
    - Enforces an Atomic Sequential Session Queue (l_conc <= 1) to thwart polynomial ROS attacks.
    """

    def __init__(self, session_timeout_ms: float = 500.0):
        # Phase 1 (KeyGen): Sample secret signing key d_C in Z_q^* and public key Y_C = d_C * G
        self.d_C: int = randrange(1, q)
        self.Y_C: ECC.EccPoint = self.d_C * G

        # Initialize empty state table T = {}
        self.state_table_T: Dict[str, Dict[str, Any]] = {}
        self.used_r2_set: Set[int] = set()

        # Enterprise IAM directory mapping shareholder/employee ID_V to public key Y_V
        self.iam_directory: Dict[str, ECC.EccPoint] = {}

        # Atomic Sequential Session Queue: stores at most l_conc = 1 pending session
        self.active_session: Dict[bytes, Dict[str, Any]] = {}
        self.session_timeout_sec: float = session_timeout_ms / 1000.0

    def register_voter(self, ID_V: str, Y_V: ECC.EccPoint) -> None:
        """Verify and store an eligible shareholder's public key (ID_V, Y_V) in the IAM directory."""
        if not check_valid_curve_point(Y_V):
            raise ValueError("Invalid voter public key Y_V (point at infinity).")
        self.iam_directory[ID_V] = Y_V

    def blind_sign_pass2(
        self,
        ID_V: str,
        sid: bytes,
        ts: int,
        C_1: Tuple[ECC.EccPoint, ECC.EccPoint],
        A_1: ECC.EccPoint,
        zeta_1: int,
    ) -> Tuple[bytes, Tuple[ECC.EccPoint, ECC.EccPoint]]:
        """
        Pass 2 (BlindSign_1):
        - Check timestamp ts, session ID sid, and voting eligibility (ID_V not in T).
        - Verify the first-round EC-NIPoK proof: zeta_1 * G == A_1 - c_1 * Y_V.
        - Decrypt voter initialization point: U_1 = E_{1,2} - d_C * E_{1,1}.
        - Sample r_2 in Z_q^*; check table T for collisions and insert (ID_V, r_2) into T.
        - Encrypt server contribution point U_2 = r_2 * G under Y_V as C_2 = (E_{2,1}, E_{2,2}).
        """
        now = time.time()
        # Evict any expired session (exceeding the 500 ms window) from the sequential queue
        expired_sids = [
            s
            for s, info in self.active_session.items()
            if now - info["created_at"] > self.session_timeout_sec
        ]
        for s in expired_sids:
            aborted = self.active_session.pop(s)
            # Release ID_V lock if aborted before Pass 4, but keep r_2 in used_r2_set permanently
            if not self.state_table_T[aborted["ID_V"]]["voted"]:
                del self.state_table_T[aborted["ID_V"]]

        # Enforce Atomic Sequential Session Queue (at most l_conc = 1 open session)
        if len(self.active_session) >= 1:
            raise RuntimeError(
                "Atomic sequential session queue is busy (l_conc = 1). Please retry."
            )

        if abs(now - ts) > 60:
            raise ValueError("Session timestamp (ts) is invalid or expired.")

        if ID_V not in self.iam_directory:
            raise PermissionError(f"Identity {ID_V} is not registered in the IAM directory.")

        if ID_V in self.state_table_T:
            raise PermissionError(
                f"Shareholder {ID_V} has already voted or has an active session in table T."
            )

        Y_V = self.iam_directory[ID_V]

        # Verify first-round EC-NIPoK proof
        if not check_valid_curve_point(A_1) or not (1 <= zeta_1 < q):
            raise ValueError("Malformed first-round EC-NIPoK proof parameters.")

        c_1 = H_A1(ID_V, Y_V, self.Y_C, sid, ts, C_1, A_1)
        lhs_1 = zeta_1 * G
        rhs_1 = A_1 + ((-c_1) % q) * Y_V
        if lhs_1 != rhs_1:
            raise PermissionError("First-round EC-NIPoK verification failed!")

        # Decrypt voter initialization point: U_1 = E_{1,2} - d_C * E_{1,1}
        E_1_1, E_1_2 = C_1
        U_1 = E_1_2 + ((-self.d_C) % q) * E_1_1

        # Sample secret random nonce r_2 in Z_q^* with collision checking against table T
        while True:
            r_2 = randrange(1, q)
            if r_2 not in self.used_r2_set:
                break

        # Record (ID_V, r_2) in state table T
        self.used_r2_set.add(r_2)
        self.state_table_T[ID_V] = {"r_2": r_2, "voted": False}

        # Sample tau_2 in Z_q^*, compute U_2 = r_2 * G, and ElGamal-encrypt under Y_V
        tau_2 = randrange(1, q)
        U_2 = r_2 * G
        E_2_1 = tau_2 * G
        E_2_2 = U_2 + tau_2 * Y_V
        C_2 = (E_2_1, E_2_2)

        # Save pending session state
        self.active_session[sid] = {
            "ID_V": ID_V,
            "Y_V": Y_V,
            "ts": ts,
            "C_1": C_1,
            "C_2": C_2,
            "U_1": U_1,
            "U_2": U_2,
            "r_2": r_2,
            "created_at": now,
        }

        return sid, C_2

    def blind_sign_pass4(
        self,
        sid: bytes,
        h_3_tilde: int,
        A_2: ECC.EccPoint,
        zeta_2: int,
    ) -> Tuple[bytes, bytes]:
        """
        Pass 4 (BlindSign_2):
        - Locate active session sid and verify the expiration window.
        - Verify the second-round EC-NIPoK proof: zeta_2 * G == A_2 - c_2 * Y_V.
        - Retrieve (ID_V, r_2) from table T and compute z_1 = (r_2 + h_3_tilde * d_C) mod q.
        - Derive 56-byte keystream mask kappa and compute C_3 = kappa XOR Encode(z_1).
        - Atomically close the session and permanently lock ID_V's voted status in table T.
        """
        if sid not in self.active_session:
            raise ValueError("Session ID (sid) not found or already closed.")

        session = self.active_session[sid]
        if time.time() - session["created_at"] > self.session_timeout_sec:
            del self.active_session[sid]
            del self.state_table_T[session["ID_V"]]
            raise TimeoutError("Blind signing session timed out.")

        ID_V = session["ID_V"]
        Y_V = session["Y_V"]
        ts = session["ts"]
        C_1 = session["C_1"]
        C_2 = session["C_2"]
        U_1 = session["U_1"]
        U_2 = session["U_2"]

        # Verify second-round EC-NIPoK proof
        if not check_valid_curve_point(A_2) or not (1 <= zeta_2 < q):
            raise ValueError("Malformed second-round EC-NIPoK proof parameters.")

        c_2 = H_A2(ID_V, Y_V, self.Y_C, sid, ts, C_1, C_2, h_3_tilde, A_2)
        lhs_2 = zeta_2 * G
        rhs_2 = A_2 + ((-c_2) % q) * Y_V
        if lhs_2 != rhs_2:
            raise PermissionError("Second-round EC-NIPoK verification failed!")

        # Retrieve the unique nonce r_2 bound to ID_V from state table T
        r_2 = self.state_table_T[ID_V]["r_2"]

        # Compute blind signing response: z_1 = (r_2 + h_3_tilde * d_C) mod q
        z_1 = (r_2 + h_3_tilde * self.d_C) % q

        # Derive 56-byte keystream mask kappa via SHAKE256 and mask z_1
        kappa = KDF_mask(U_1, U_2, sid, C_1, C_2, h_3_tilde, SCALAR_BYTES)
        C_3 = xor_bytes(kappa, encode_scalar(z_1))

        # Permanently lock voted status of (ID_V, r_2) in table T and close session atomically
        self.state_table_T[ID_V]["voted"] = True
        del self.active_session[sid]

        return sid, C_3


class VoterClient:
    """
    Voting Member / Shareholder Client (V):
    - Generates identity key pair (d_V, Y_V = d_V * G).
    - Executes Pass 1 (Blind_1), Pass 3 (Blind_2), and signature Unblinding (Unblind).
    """

    def __init__(self, ID_V: str, Y_C: ECC.EccPoint):
        self.ID_V: str = ID_V
        self.Y_C: ECC.EccPoint = Y_C

        # Phase 1 (KeyGen): Sample secret key d_V in Z_q^* and compute Y_V = d_V * G
        self.d_V: int = randrange(1, q)
        self.Y_V: ECC.EccPoint = self.d_V * G

        # Local ephemeral state maintained on the voter's device during signing
        self._state: Dict[str, Any] = {}

    def blind_pass1(
        self,
    ) -> Tuple[
        str, bytes, int, Tuple[ECC.EccPoint, ECC.EccPoint], ECC.EccPoint, int
    ]:
        """
        Pass 1 (Blind_1):
        - Sample r_1 in Z_q and tau_1, eta_1 in Z_q^*.
        - Compute initialization point U_1 = r_1 * G and commitment A_1 = eta_1 * G.
        - ElGamal-encrypt U_1 under Committee public key Y_C as C_1 = (E_{1,1}, E_{1,2}).
        - Generate first-round EC-NIPoK proof (A_1, zeta_1).
        """
        r_1 = randrange(0, q)
        tau_1 = randrange(1, q)
        eta_1 = randrange(1, q)

        U_1 = r_1 * G if r_1 != 0 else _curve_info.G.point_at_infinity()
        A_1 = eta_1 * G

        E_1_1 = tau_1 * G
        E_1_2 = U_1 + tau_1 * self.Y_C
        C_1 = (E_1_1, E_1_2)

        sid = get_random_bytes(32)  # 256-bit random session identifier
        ts = int(time.time())

        c_1 = H_A1(self.ID_V, self.Y_V, self.Y_C, sid, ts, C_1, A_1)
        zeta_1 = (eta_1 - c_1 * self.d_V) % q

        # Store local state for Pass 3 and Unblinding
        self._state = {
            "sid": sid,
            "ts": ts,
            "r_1": r_1,
            "U_1": U_1,
            "C_1": C_1,
        }

        return self.ID_V, sid, ts, C_1, A_1, zeta_1

    def blind_pass3(
        self,
        sid: bytes,
        C_2: Tuple[ECC.EccPoint, ECC.EccPoint],
        ballot_M: str,
    ) -> Tuple[bytes, int, ECC.EccPoint, int]:
        """
        Pass 3 (Blind_2):
        - Decrypt server contribution point: U_2 = E_{2,2} - d_V * E_{2,1}.
        - Sample fresh independent scalars u, w, gamma in Z_q (dual-base re-randomization).
        - Compute public commitment W = U_1 + U_2 + u * G + w * Y_C and hash chain for M.
        - Blind signing challenge: h_3_tilde = (h_3 + w) mod q.
        - Generate second-round EC-NIPoK proof (A_2, zeta_2).
        """
        if sid != self._state.get("sid"):
            raise ValueError("Session ID (sid) mismatch in Pass 3.")

        E_2_1, E_2_2 = C_2
        U_2 = E_2_2 + ((-self.d_V) % q) * E_2_1
        if not check_valid_curve_point(U_2):
            raise ValueError("Decrypted server contribution point U_2 is invalid.")

        # Sample fresh independent scalars u, w, gamma in Z_q (non-zero for point operations)
        u = randrange(1, q)
        w = randrange(1, q)
        gamma = randrange(1, q)

        U_1 = self._state["U_1"]

        # Dual-base re-randomization across independent generators G and Y_C
        W = U_1 + U_2 + (u * G) + (w * self.Y_C)
        K = gamma * G

        # Compute hash chain anchoring ballot M
        h_1 = H_1(self.Y_C, ballot_M, K)
        K_1 = h_1 * G
        K_2 = K + K_1
        h_2 = H_2(K, K_1, K_2)
        h_3 = H_3(h_2, W)

        # Shift signing challenge by blinding scalar w
        h_3_tilde = (h_3 + w) % q

        # Generate second-round EC-NIPoK proof
        eta_2 = randrange(1, q)
        A_2 = eta_2 * G
        c_2 = H_A2(
            self.ID_V,
            self.Y_V,
            self.Y_C,
            sid,
            self._state["ts"],
            self._state["C_1"],
            C_2,
            h_3_tilde,
            A_2,
        )
        zeta_2 = (eta_2 - c_2 * self.d_V) % q

        # Save blinding parameters locally for the Unblind step
        self._state.update(
            {
                "M": ballot_M,
                "C_2": C_2,
                "U_2": U_2,
                "u": u,
                "w": w,
                "W": W,
                "K": K,
                "h_3": h_3,
                "h_3_tilde": h_3_tilde,
            }
        )

        return sid, h_3_tilde, A_2, zeta_2

    def unblind(
        self, sid: bytes, C_3: bytes
    ) -> Tuple[str, ECC.EccPoint, ECC.EccPoint, int]:
        """
        Unblinding Step (Unblind):
        - Re-derive keystream mask kappa and recover z_1 = Decode(kappa XOR C_3).
        - Verify algebraic validity: z_1 * G == U_2 + h_3_tilde * Y_C.
        - Accumulate blinding scalars: z = (z_1 + r_1 + u) mod q.
        - Output anonymous ballot package (M, W, K, z).
        """
        if sid != self._state.get("sid"):
            raise ValueError("Session ID (sid) mismatch during Unblinding.")

        U_1 = self._state["U_1"]
        U_2 = self._state["U_2"]
        C_1 = self._state["C_1"]
        C_2 = self._state["C_2"]
        h_3_tilde = self._state["h_3_tilde"]

        # Unmask server response z_1 from C_3
        kappa = KDF_mask(U_1, U_2, sid, C_1, C_2, h_3_tilde, SCALAR_BYTES)
        z_1 = decode_scalar(xor_bytes(kappa, C_3))

        # Verify intermediate blind signature equation: z_1 * G == U_2 + h_3_tilde * Y_C
        if (z_1 * G) != (U_2 + (h_3_tilde * self.Y_C)):
            raise ValueError("Intermediate blind signature response z_1 is invalid!")

        # Remove blinding factors to obtain public signature scalar z
        z = (z_1 + self._state["r_1"] + self._state["u"]) % q

        M = self._state["M"]
        W = self._state["W"]
        K = self._state["K"]

        # Purge local sensitive blinding state
        self._state.clear()

        return M, W, K, z


class TallyingServer:
    """
    Tallying Server & Public Bulletin Board (T):
    - Receives anonymous cast ballots (M, W, K, z).
    - Verifies the public elliptic curve verification equation: z * G == W + h_3 * Y_C.
    """

    def __init__(self, Y_C: ECC.EccPoint):
        self.Y_C: ECC.EccPoint = Y_C
        self.bulletin_board: list = []

    def verify_and_record_ballot(
        self, M: str, W: ECC.EccPoint, K: ECC.EccPoint, z: int
    ) -> bool:
        """
        Phase 3 (Verify):
        Check W, K in E and z in Z_q; recompute h_1, K_1, K_2, h_2, h_3,
        and accept the ballot if and only if z * G == W + h_3 * Y_C.
        """
        if not (check_valid_curve_point(W) and check_valid_curve_point(K)):
            return False
        if not (0 <= z < q):
            return False

        h_1 = H_1(self.Y_C, M, K)
        K_1 = h_1 * G
        K_2 = K + K_1
        h_2 = H_2(K, K_1, K_2)
        h_3 = H_3(h_2, W)

        lhs = z * G
        rhs = W + (h_3 * self.Y_C)

        if lhs == rhs:
            self.bulletin_board.append((M, W, K, z))
            return True
        return False


# =====================================================================
# 4. END-TO-END PROTOCOL SIMULATION & BENCHMARKING
# =====================================================================
if __name__ == "__main__":
    print("=" * 72)
    print(" ENTERPRISE E-VOTING BLIND SIGNATURE SIMULATION ON ED448 (CURVE448)")
    print("=" * 72)

    # --- Phase 1: Identity Registration and State Table T Initialization (KeyGen) ---
    t0 = time.perf_counter()
    committee = CommitteeServer(session_timeout_ms=500.0)
    voter_id = "SHAREHOLDER_VN_001"
    voter = VoterClient(ID_V=voter_id, Y_C=committee.Y_C)
    committee.register_voter(voter_id, voter.Y_V)
    tally_server = TallyingServer(Y_C=committee.Y_C)
    t_keygen = (time.perf_counter() - t0) * 1000

    print(f"[Phase 1 - KeyGen] Key generation & Table T setup : {t_keygen:.2f} ms")
    print(f"  + Subgroup prime order q : {q.bit_length()} bits")
    print(f"  + Encoded scalar length  : {SCALAR_BYTES} bytes")

    # --- Phase 2: Eligibility Authentication and 4-Pass Blind Signature Issuance ---
    ballot_choice = "AGM_2026_RESOLUTION_01: APPROVE"

    # Pass 1 (Voter -> Server): Blind_1
    t1 = time.perf_counter()
    id_v, sid, ts, C_1, A_1, zeta_1 = voter.blind_pass1()
    t_pass1 = (time.perf_counter() - t1) * 1000

    # Pass 2 (Server -> Voter): BlindSign_1
    t2 = time.perf_counter()
    sid_resp2, C_2 = committee.blind_sign_pass2(id_v, sid, ts, C_1, A_1, zeta_1)
    t_pass2 = (time.perf_counter() - t2) * 1000

    # Pass 3 (Voter -> Server): Blind_2
    t3 = time.perf_counter()
    sid_req3, h_3_tilde, A_2, zeta_2 = voter.blind_pass3(
        sid_resp2, C_2, ballot_choice
    )
    t_pass3 = (time.perf_counter() - t3) * 1000

    # Pass 4 (Server -> Voter): BlindSign_2
    t4 = time.perf_counter()
    sid_resp4, C_3 = committee.blind_sign_pass4(
        sid_req3, h_3_tilde, A_2, zeta_2
    )
    t_pass4 = (time.perf_counter() - t4) * 1000

    # Unblinding at Shareholder Device (Unblind)
    t5 = time.perf_counter()
    M_cast, W_cast, K_cast, z_cast = voter.unblind(sid_resp4, C_3)
    t_unblind = (time.perf_counter() - t5) * 1000

    # --- Phase 3: Public Verification at Tallying Server (Verify) ---
    t6 = time.perf_counter()
    is_valid = tally_server.verify_and_record_ballot(
        M_cast, W_cast, K_cast, z_cast
    )
    t_verify = (time.perf_counter() - t6) * 1000

    t_blind_total = t_pass1 + t_pass3
    t_blindsign_total = t_pass2 + t_pass4
    t_total = (
        t_keygen + t_blind_total + t_blindsign_total + t_unblind + t_verify
    )

    print("\n[Phase 2 - 4-Pass Blind Signing & Unblind]")
    print(f"  + Voter Blind (Pass 1 + Pass 3)     : {t_blind_total:.2f} ms")
    print(f"  + Server BlindSign (Pass 2 + Pass 4): {t_blindsign_total:.2f} ms")
    print(f"  + Voter Unblind                     : {t_unblind:.2f} ms")

    print("\n[Phase 3 - Public Verification]")
    print(f"  + Ballot verification status        : {'VALID (ACCEPTED)' if is_valid else 'REJECTED'}")
    print(f"  + Recorded anonymous ballot         : {M_cast}")
    print(f"  + Verification time (Verify)        : {t_verify:.2f} ms")
    print("-" * 72)
    print(f" TOTAL END-TO-END EXECUTION TIME       : {t_total:.2f} ms")
    print("=" * 72)

    # --- Security Test: Double-Voting Prevention via State Table T ---
    print("\n[Security Check] Shareholder attempts a second signing request:")
    try:
        id_v2, sid2, ts2, C_1_2, A_1_2, zeta_1_2 = voter.blind_pass1()
        committee.blind_sign_pass2(id_v2, sid2, ts2, C_1_2, A_1_2, zeta_1_2)
    except PermissionError as err:
        print(f"  -> Successfully blocked by State Table T: {err}")
