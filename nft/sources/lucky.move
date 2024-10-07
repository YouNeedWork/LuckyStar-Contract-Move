module nft::lucky {
    use sui::package;
    use sui::display;

    use sui::tx_context::TxContext;
    use sui::tx_context;
    use sui::transfer::{public_transfer, public_share_object, transfer};
    use std::string::{utf8, String};
    use sui::object::{UID};
    use sui::object;
    use std::string;
    use sui::transfer_policy;
    use nft::rule;
    #[test_only]
    use sui::test_scenario;
    #[test_only]
    use sui::test_scenario::{next_tx, end};
    #[test_only]
    use sui::test_utils;

    struct LUCKY has drop {}

    struct LuckyNFT has key,store{
        id:UID,
        name:String,
        img_url:String,
        level:u64,
        point:u64,
    }

    struct MintCap has key {
        id:UID,
    }

    struct BurnCap has key {
        id:UID,
    }


    const SHOW_NAME: vector<u8> = b"LuckySart";
    const BASE_URI_I: vector<u8> = b"https://luckystar-nft.s3.ap-southeast-1.amazonaws.com/imgs/level-1.png";
    const BASE_URI_II: vector<u8> = b"https://luckystar-nft.s3.ap-southeast-1.amazonaws.com/imgs/level-2.png";
    const BASE_URI_III: vector<u8> = b"https://luckystar-nft.s3.ap-southeast-1.amazonaws.com/imgs/level-3.png";
    const BASE_URI_IV: vector<u8> = b"https://luckystar-nft.s3.ap-southeast-1.amazonaws.com/imgs/level-4.png";
    const BASE_URI_V: vector<u8> = b"https://luckystar-nft.s3.ap-southeast-1.amazonaws.com/imgs/level-5.png";


    const DECIMAL:u64 = 1000000000;

    const LUCKYSTAR_NFT_I: u64 = 1;
    const LUCKYSTAR_NFT_II: u64 = 2;
    const LUCKYSTAR_NFT_III: u64 = 3;
    const LUCKYSTAR_NFT_IV: u64 = 4;
    const LUCKYSTAR_NFT_V: u64 = 5;

    const LUCKYSTAR_NFT_POINT_I: u64 = 1;
    const LUCKYSTAR_NFT_POINT_II: u64 = 999 * 1000000000;
    const LUCKYSTAR_NFT_POINT_III: u64 = 1999 * 1000000000;
    const LUCKYSTAR_NFT_POINT_IV: u64 = 3999 * 1000000000;
    const LUCKYSTAR_NFT_POINT_V: u64 = 7999 * 1000000000;


    fun init(otw:LUCKY,ctx:&mut TxContext){
        //let base_uri = b"https://cloudflare-ipfs.com/ipfs/QmTQ2cafNCn9NvymbjE8LRXexo89anFJyASmkQcESmcgCm";
        let publisher = package::claim(otw, ctx);
        let (policy,cap) = transfer_policy::new<LuckyNFT>(&publisher,ctx);

        rule::add<LuckyNFT>(&mut policy,&cap,500,1000);

        public_transfer(cap,tx_context::sender(ctx));
        public_share_object(policy);

        let keys = vector[
            utf8(b"name"),
            utf8(b"link"),
            utf8(b"image_url"),
            utf8(b"description"),
            utf8(b"project_url"),
            utf8(b"creator"),
        ];

        let values = vector[
            // For `name` one can use the `Hero.name` property
            utf8(b"{name}"),
            // For `link` one can build a URL using an `id` property
            utf8(b"https://www.luckystar.homes/"),
            // For `image_url` use an IPFS template + `img_url` property.
            utf8(b"{img_url}"),
            // Description is static for all `Hero` objects.
            utf8(b"LuckyStar has its unique star sign NFT series which could boost your earning while you play lucky games. LuckyStar NFT supports functions as staking, upgrading, boosting, trading and more."),
            // Project URL is usually static
            utf8(b"https://www.luckystar.homes/"),
            // Creator field can be any
            utf8(SHOW_NAME)
        ];

        // Get a new `Display` object for the `Hero` type.
        let display = display::new_with_fields<LuckyNFT>(
            &publisher, keys, values, ctx
        );

        // Commit first version of `Display` to apply changes.
        display::update_version(&mut display);

        public_transfer(publisher, tx_context::sender(ctx));
        public_transfer(display, tx_context::sender(ctx));

        transfer(MintCap{id:object::new(ctx)}, tx_context::sender(ctx));
        transfer(BurnCap{id:object::new(ctx)}, tx_context::sender(ctx));
    }

    public fun mint(_:&MintCap,ctx:&mut TxContext):LuckyNFT {
        LuckyNFT{
            id:object::new(ctx),
            name:string::utf8(SHOW_NAME),
            img_url:string::utf8(BASE_URI_I),
            level:LUCKYSTAR_NFT_I,
            point:0,
        }
    }

    public entry fun mint_to_sender(cap:&MintCap,ctx:&mut TxContext) {
        public_transfer(mint(cap,ctx),tx_context::sender(ctx));
    }

    public entry fun mint_and_transfer(cap:&MintCap,addr:address,ctx:&mut TxContext) {
        public_transfer(mint(cap,ctx),addr);
    }

    public entry fun burn(_:&BurnCap,nft:LuckyNFT,_ctx:&mut TxContext){
        let LuckyNFT{
            id,
            name:_,
            img_url:_,
            level:_,
            point:_,
        } = nft;
        object::delete(id);
    }

    public entry fun point_up(nft:&mut LuckyNFT,point:u64,_ctx:&mut TxContext){
        nft.point = nft.point + point;
        if (nft.point < LUCKYSTAR_NFT_POINT_II){
            nft.img_url = string::utf8(BASE_URI_I);
            nft.level = LUCKYSTAR_NFT_I;
        } else if (nft.point < LUCKYSTAR_NFT_POINT_III){
            nft.img_url = string::utf8(BASE_URI_II);
            nft.level = LUCKYSTAR_NFT_II;
        } else if (nft.point < LUCKYSTAR_NFT_POINT_IV){
            nft.img_url = string::utf8(BASE_URI_III);
            nft.level = LUCKYSTAR_NFT_III;
        } else if (nft.point < LUCKYSTAR_NFT_POINT_V){
            nft.img_url = string::utf8(BASE_URI_IV);
            nft.level = LUCKYSTAR_NFT_IV;
        } else {
            nft.img_url = string::utf8(BASE_URI_V);
            nft.level = LUCKYSTAR_NFT_V;
        }
    }

    public entry fun level(nft:&LuckyNFT):u64 {
        nft.level
    }

    public entry fun point(nft:&LuckyNFT):u64 {
        nft.point
    }
    #[test_onlu]
    public fun mint_for_test(ctx:&mut TxContext):LuckyNFT{
        let mint_cap = MintCap{id:object::new(ctx)};
        let nft = mint(&mint_cap,ctx);
        let MintCap{id} = mint_cap;
        object::delete(id);
        nft
    }


    #[test]
    fun test_mint(){
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let mint = MintCap{id:object::new(&mut ctx)};
        //let burn = BurnCap{id:object::new(&mut ctx)};
        mint_to_sender(&mint,&mut ctx);
        next_tx(&mut scenario,sender);
        let nft = test_scenario::take_from_sender<LuckyNFT>(&mut scenario);

        test_utils::destroy(mint);
        test_utils::destroy(nft);
        end(scenario);
    }

    #[test]
    fun test_burn(){
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let mint = MintCap{id:object::new(&mut ctx)};
        let burn = BurnCap{id:object::new(&mut ctx)};
        mint_to_sender(&mint,&mut ctx);
        next_tx(&mut scenario,sender);
        let nft = test_scenario::take_from_sender<LuckyNFT>(&mut scenario);
        burn(&burn,nft,&mut ctx);
        test_utils::destroy(mint);


        test_utils::destroy(burn);
        end(scenario);
    }

    #[test]
    fun test_level_and_point(){
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let mint = MintCap{id:object::new(&mut ctx)};
        let burn = BurnCap{id:object::new(&mut ctx)};
        mint_to_sender(&mint,&mut ctx);
        next_tx(&mut scenario,sender);
        let nft = test_scenario::take_from_sender<LuckyNFT>(&mut scenario);
        assert!(level(&nft)==1,1);
        assert!(point(&nft)==0,1);
        point_up(&mut nft,LUCKYSTAR_NFT_POINT_II,&mut ctx);
        assert!(level(&nft)==LUCKYSTAR_NFT_II,1);
        assert!(point(&nft)==LUCKYSTAR_NFT_POINT_II,1);
        point_up(&mut nft,LUCKYSTAR_NFT_POINT_III,&mut ctx);
        assert!(level(&nft)==LUCKYSTAR_NFT_III,1);
        assert!(point(&nft)==LUCKYSTAR_NFT_POINT_II+LUCKYSTAR_NFT_POINT_III,1);
        point_up(&mut nft,LUCKYSTAR_NFT_POINT_IV,&mut ctx);
        assert!(level(&nft)==LUCKYSTAR_NFT_IV,1);
        assert!(point(&nft)==LUCKYSTAR_NFT_POINT_II+LUCKYSTAR_NFT_POINT_III+LUCKYSTAR_NFT_POINT_IV,1);
        point_up(&mut nft,LUCKYSTAR_NFT_POINT_V,&mut ctx);
        assert!(level(&nft)==LUCKYSTAR_NFT_V,1);
        assert!(point(&nft)==LUCKYSTAR_NFT_POINT_II+LUCKYSTAR_NFT_POINT_III+LUCKYSTAR_NFT_POINT_IV+LUCKYSTAR_NFT_POINT_V,1);

        burn(&burn,nft,&mut ctx);
        test_utils::destroy(mint);
        test_utils::destroy(burn);
        end(scenario);
    }
}
