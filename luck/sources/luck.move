module luck::luck {
    use sui::tx_context::TxContext;
    use sui::coin::{create_currency, mint};
    use std::option::some;
    use sui::transfer;
    use sui::url;
    use sui::tx_context;
    use sui::transfer::{public_freeze_object};
    #[test_only]
    use sui::coin::Coin;

    struct LUCK has drop{}

    fun init(winer: LUCK, ctx:&mut TxContext) {
        let (mint_able,metadata) = create_currency<LUCK>(winer,9,b"LUCK",b"LUCKYSTAR",b"LUCKYSTAR TOKEN",some(url::new_unsafe_from_bytes(b"https://luckystar-web.s3.ap-southeast-1.amazonaws.com/starlogo.svg")),ctx);
        public_freeze_object(metadata);
        let coin = mint(&mut mint_able,4000000000*1000000000,ctx);
        public_freeze_object(mint_able);
        transfer::public_transfer(coin,tx_context::sender(ctx))
    }


    #[test_only]
    public fun test_mint(ctx:&mut TxContext):Coin<LUCK> {
        let winer = LUCK {};
        let (mint_able,metadata) = create_currency<LUCK>(winer,9,b"Luck",b"Luck",b"The coin for Luck",some(url::new_unsafe_from_bytes(b"https://www.luckystar.homes/_next/static/media/logo.0fcacc03.svg")),ctx);
        public_freeze_object(metadata);

        let coin = mint(&mut mint_able,15*100000000,ctx);
        public_freeze_object(mint_able);

        coin
    }
}
