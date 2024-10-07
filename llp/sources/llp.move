module llp::llp {
    use sui::tx_context::TxContext;
    use sui::coin::{create_currency, mint};
    use std::option::some;
    use sui::transfer;
    use sui::url;
    use sui::tx_context;
    use sui::transfer::{public_freeze_object};
    struct LLP has drop{}

    fun init(winer: LLP, ctx:&mut TxContext) {
        let (mint_able,metadata) = create_currency<LLP>(winer,9,b"LLP",b"LLP",b"The coin for Luck",some(url::new_unsafe_from_bytes(b"https://www.luckystar.homes/_next/static/media/logo.0fcacc03.svg")),ctx);
        public_freeze_object(metadata);
        let coin = mint(&mut mint_able,1500000000*1000000000,ctx);
        transfer::public_transfer(mint_able,tx_context::sender(ctx));
        transfer::public_transfer(coin,tx_context::sender(ctx))
    }
}
