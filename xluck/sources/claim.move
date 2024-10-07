module xluck::claim {
    use std::vector;

    use sui::bag::{Self, Bag};
    use sui::clock::{Self, Clock};
    use sui::event;
    use sui::object::{Self, UID, ID};
    use sui::transfer::{public_transfer, public_share_object};
    use sui::tx_context::{Self, TxContext};
    use token::nonTransferCoin::{Self, NonTransferCoin};

    const E_OWNER_ONLY: u64 = 1000;
    const E_EMERGENCY_ON: u64 = 1001;
    const E_NOT_NEED_CLAIM: u64 = 1002;
    const E_ARGS_NOT_MATCH: u64 = 1003;
    const E_NOT_STARTED: u64 = 1004;


    struct ManageCap<phantom T> has key, store {
        id: UID,
        claim_id: ID,
    }

    struct Claim<phantom T> has key, store {
        id: UID,
        emergency: bool,
        start_time: u64,
        end_time: u64,
        balance: NonTransferCoin<T>,
        claim_members: Bag,
        unclaim_members: Bag,
    }

    public entry fun create_claim<T>(c: NonTransferCoin<T>, start_time: u64, end_time: u64, ctx: &mut TxContext) {
        let claim = Claim {
            id: object::new(ctx),
            emergency: false,
            start_time,
            end_time,
            balance: c,
            claim_members: bag::new(ctx),
            unclaim_members: bag::new(ctx),
        };
        let manage_cap = ManageCap<T> {
            id: object::new(ctx),
            claim_id: object::id(&claim),
        };
        public_transfer(manage_cap, tx_context::sender(ctx));
        public_share_object(claim);
    }

    struct ClaimEvent has copy, drop {
        address: address,
        amount: u64,
    }

    public entry fun claim<T>(c: &mut Claim<T>, clock: &Clock, ctx: &mut TxContext) {
        assert!(!c.emergency, E_EMERGENCY_ON);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&c.unclaim_members, sender), E_NOT_NEED_CLAIM);

        let current_time = clock::timestamp_ms(clock);
        assert!(current_time >= c.start_time && current_time <= c.end_time, E_NOT_STARTED);

        if (bag::contains(&c.claim_members, sender)) {
            let wait_cliam_amount = bag::borrow<address, u64>(&c.unclaim_members, sender);
            let claim_amount = bag::borrow_mut<address, u64>(&mut c.claim_members, sender);
            assert!(*wait_cliam_amount > *claim_amount, E_NOT_NEED_CLAIM);

            let claim = nonTransferCoin::split(&mut c.balance, sender, *wait_cliam_amount - *claim_amount, ctx);
            *claim_amount = *wait_cliam_amount;
            public_transfer(claim, sender);

            event::emit(ClaimEvent {
                address: sender,
                amount: *wait_cliam_amount - *claim_amount,
            });
        } else {
            let wait_cliam_amount = bag::borrow<address, u64>(&c.unclaim_members, sender);
            let claim = nonTransferCoin::split(&mut c.balance, sender, *wait_cliam_amount, ctx);
            bag::add(&mut c.claim_members, sender, *wait_cliam_amount);
            public_transfer(claim, sender);
            event::emit(ClaimEvent {
                address: sender,
                amount: *wait_cliam_amount,
            });
        }
    }

    public entry fun add_wait_claim_list<T>(
        c: &mut Claim<T>,
        adm: &ManageCap<T>,
        list: vector<address>,
        amounts: vector<u64>,
    ) {
        assert!(object::id(c) == adm.claim_id, E_OWNER_ONLY);
        let length = vector::length(&list);
        assert!(length == vector::length(&amounts), E_ARGS_NOT_MATCH);

        let i = 0;
        while (i < length) {
            let ads = vector::pop_back(&mut list);
            let amount = vector::pop_back(&mut amounts);
            if (bag::contains(&c.unclaim_members, ads)) {
                let amt = bag::borrow_mut<address, u64>(&mut c.unclaim_members, ads);
                *amt = amount;
            } else {
                bag::add(&mut c.unclaim_members, ads, amount);
            };
            i = i + 1;
        }
    }

    public entry fun emergency_switch<T>(c: &mut Claim<T>, adm: &ManageCap<T>) {
        assert!(object::id(c) == adm.claim_id, E_OWNER_ONLY);
        c.emergency = !c.emergency
    }

    public entry fun emergency_withdraw<T>(c: &mut Claim<T>, adm: &ManageCap<T>, ctx: &mut TxContext) {
        assert!(object::id(c) == adm.claim_id, E_OWNER_ONLY);
        let val = nonTransferCoin::value(&c.balance);
        let c = nonTransferCoin::split(&mut c.balance, tx_context::sender(ctx), val, ctx);
        public_transfer(c, tx_context::sender(ctx));
    }

    public entry fun emergency_depost<T>(
        c: &mut Claim<T>,
        adm: &ManageCap<T>,
        paid: NonTransferCoin<T>,
        _ctx: &mut TxContext
    ) {
        assert!(object::id(c) == adm.claim_id, E_OWNER_ONLY);
        nonTransferCoin::join(&mut c.balance, paid);
    }
}
