module esluck::esLuck {
    use sui::tx_context::TxContext;
    use sui::tx_context;
    use sui::balance;
    use sui::transfer::{public_transfer};
    use sui::balance::{Supply};
    use sui::object;
    use sui::object::UID;
    use token::nonTransferCoin::from_balance;
    #[test_only]
    use token::nonTransferCoin::NonTransferCoin;

    const DECIMIAL :u64= 100000000;
    struct ESLUCK has drop {}

    struct MintAbility<phantom T> has key,store {
        id:UID,
        supply:Supply<T>
    }

    fun init(winner:ESLUCK,ctx:&mut TxContext) {
        let supply = balance::create_supply(winner);
        let sender = tx_context::sender(ctx);

        let cap = MintAbility{id:object::new(ctx),supply};
        mint(&mut cap,4000000000*1000000000,ctx);

        public_transfer(cap,sender)
    }

    #[test_only]
    public fun test_init(ctx:&mut TxContext):MintAbility<ESLUCK> {
        let winner = ESLUCK{};
        let supply = balance::create_supply(winner);
        //let sender = tx_context::sender(ctx);
        MintAbility{id:object::new(ctx),supply}
    }


    public entry fun mint<T>(adm:&mut MintAbility<T>,amount:u64,ctx:&mut TxContext){
        let blc = balance::increase_supply(&mut adm.supply,amount);
        let coin = from_balance(blc,tx_context::sender(ctx),ctx);
        public_transfer(coin,tx_context::sender(ctx))
    }

    #[test_only]
    public fun test_mint<T>(adm:&mut MintAbility<T>,amount:u64,ctx:&mut TxContext):NonTransferCoin<T>{
        let blc = balance::increase_supply(&mut adm.supply,amount);
        let coin = from_balance(blc,tx_context::sender(ctx),ctx);
        coin
    }
}