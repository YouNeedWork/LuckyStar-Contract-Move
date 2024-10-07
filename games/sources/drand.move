module games::drand {

    use std::hash::sha2_256;
    use std::vector;

    use sui::bls12381;
    #[test_only]
    use std::debug::print;

    /// Error codes
    const EInvalidRndLength: u64 = 0;
    const EInvalidProof: u64 = 1;


    const GENESIS: u64 = 1595431050;

    const DRAND_PK: vector<u8> =
        x"868f005eb8e6e4ca0a47c8a77ceaa5309a47978a7c71bc5cce96366b5d7a569937c529eeda66c7293784a9402801af31";

    /// Check that a given epoch time has passed by verifying a drand signature from a later time.
    /// round must be at least (epoch_time - GENESIS)/30 + 1).
    public fun verify_time_has_passed(epoch_time: u64, sig: vector<u8>, prev_sig: vector<u8>, round: u64) {
        assert!(epoch_time <= GENESIS + 30 * (round - 1), EInvalidProof);
        verify_drand_signature(sig, prev_sig, round);
    }

    public fun get_genesis_time():u64{
        GENESIS
    }

    /// Check a drand output.
    public fun verify_drand_signature(sig: vector<u8>, prev_sig: vector<u8>, round: u64) {
        // Convert round to a byte array in big-endian order.
        let round_bytes: vector<u8> = vector[0, 0, 0, 0, 0, 0, 0, 0];
        let i = 7;
        while (i > 0) {
            let curr_byte = round % 0x100;
            let curr_element = vector::borrow_mut(&mut round_bytes, i);
            *curr_element = (curr_byte as u8);
            round = round >> 8;
            i = i - 1;
        };

        // Compute sha256(prev_sig, round_bytes).
        vector::append(&mut prev_sig, round_bytes);
        let digest = sha2_256(prev_sig);
        // Verify the signature on the hash.
        assert!(bls12381::bls12381_min_pk_verify(&sig, &DRAND_PK, &digest), EInvalidProof);
    }

    /// Derive a uniform vector from a drand signature.
    public fun derive_randomness(drand_sig: vector<u8>): vector<u8> {
        sha2_256(drand_sig)
    }

    // Converts the first 16 bytes of rnd to a u64 number and outputs its modulo with input n.
    // Since n is u64, the output is at most 2^{-64} biased assuming rnd is uniformly random.
    public fun safe_selection(n: u64, rnd: &vector<u8>): u64 {
        assert!(vector::length(rnd) >= 16, EInvalidRndLength);
        let m: u64 = 0;
        let i = 0;
        while (i < 16) {
            m = m << 8;
            let curr_byte = *vector::borrow(rnd, i);
            m = m + (curr_byte as u64);
            i = i + 1;
        };
        let n_128 = (n as u64);
        let module_128 = m % n_128;
        let res = (module_128 as u64);
        res
    }

    #[test]
    fun test() {
        let sig = x"a86e89206b518ac65c7a74cb24055899428e932436591be4a6e61031ca49a54cbb44f75c3a3f0da54737d0311ce5b702109312747d9a9d590dda9d72b021bb1dacf34a4f3e3027c2eb35051037ac11039ef8518ead6c828bd9139c2c8d1ab6da";
        let prev_sig = x"a92c371a680b47172a45fd7c2022d6399eb4df90f5d4a9757f13890e4cd774bc441e5c1ffc245035b32d1ec57ef5711c11c8708d1cc8d0f5bd64d7c3873655dc3d2cbb8453c11eeadf3faed01f7afeed4bdbded9040d65635ec431a786a2c8a5";
        print(&sig);
        let round = 2942294;
        verify_drand_signature(sig, prev_sig, round);
    }
}
