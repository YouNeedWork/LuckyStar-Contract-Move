module token::nonTransferCoin {
    use sui::balance;
    use sui::tx_context::TxContext;
    use sui::balance::Balance;
    use sui::object;
    use sui::object::UID;
    use std::vector;
    use sui::transfer;
    use sui::tx_context;

    struct NonTransferCoin<phantom T> has key,store {
        id: UID,
        balance: Balance<T>,
        owner: address
    }

    public fun keep<T>(c: NonTransferCoin<T>, ctx: &TxContext) {
        transfer::public_transfer(c, tx_context::sender(ctx))
    }

    public fun value<T>(c: &NonTransferCoin<T>): u64 {
        balance::value(&c.balance)
    }

    public fun owner<T>(c: &NonTransferCoin<T>): address {
        c.owner
    }

    public fun borrow<T>(coin: &NonTransferCoin<T>): &Balance<T> {
        &coin.balance
    }

    public fun borrow_mut<T>(coin: &mut NonTransferCoin<T>): &mut Balance<T> {
        &mut coin.balance
    }

    public fun zero<T>(owner: address, ctx: &mut TxContext): NonTransferCoin<T> {
        NonTransferCoin { id: object::new(ctx), balance: balance::zero(), owner }
    }

    public fun from_balance<T>(
        balance: Balance<T>, owner: address, ctx: &mut TxContext
    ): NonTransferCoin<T> {
        NonTransferCoin { id: object::new(ctx), balance, owner }
    }

    /// Destroy `RegulatedCoin` and return its `Balance`;
    public fun into_balance<T>(coin: NonTransferCoin<T>): Balance<T> {
        let NonTransferCoin { balance, owner: _, id } = coin;
        sui::object::delete(id);
        balance
    }

    public fun join<T>(c1: &mut NonTransferCoin<T>, c2: NonTransferCoin<T>) {
        balance::join(&mut c1.balance, into_balance(c2));
    }

    public entry fun join_vec<T>(c1: &mut NonTransferCoin<T>, coins: vector<NonTransferCoin<T>>) {
        let (i, len) = (0, vector::length(&coins));
        while (i < len) {
            let coin = vector::pop_back(&mut coins);
            join(c1, coin);
            i = i + 1
        };
        vector::destroy_empty(coins)
    }

    public fun split<T>(
        c1: &mut NonTransferCoin<T>, creator: address, value: u64, ctx: &mut TxContext
    ): NonTransferCoin<T> {
        let balance = balance::split(&mut c1.balance, value);
        from_balance(balance, creator, ctx)
    }

    public fun destroy_zero<T>(coin: NonTransferCoin<T>) {
        let NonTransferCoin<T>{
            id,
            balance:blc,
            owner: _,
        } = coin;

        balance::destroy_zero(blc);
        object::delete(id);
    }

    public fun destroy_zero_or_transfer<T>(
        coin: NonTransferCoin<T>,
        ctx: &mut TxContext
    ) {
        if (value(&coin) == 0) {
            destroy_zero(coin);
        } else {
            transfer::public_transfer(coin, tx_context::sender(ctx));
        };
    }

    public entry fun split_vec<T>(
        self: &mut NonTransferCoin<T>, split_amounts: vector<u64>, ctx: &mut TxContext
    ) {
        let (i, len) = (0, vector::length(&split_amounts));
        while (i < len) {
            keep(split(self, tx_context::sender(ctx),*vector::borrow(&split_amounts, i), ctx),ctx);
            i = i + 1;
        };
    }

    public entry fun split_and_keep<T>(
        self: &mut NonTransferCoin<T>, split_amount: u64, ctx: &mut TxContext
    ) {
        keep(split(self, tx_context::sender(ctx),split_amount, ctx), ctx)
    }
}
