module games::vault {
    use sui::coin::{Self, Coin};
    use sui::object::{Self, UID};
    use sui::transfer::{public_share_object, public_transfer};
    use sui::tx_context::{Self, TxContext};
    use sui::vec_map::{Self, VecMap};

    friend games::coinFlip;
    friend games::range;
    friend games::raffle;
    friend games::wheel;
    friend games::game_controller;

    #[test_only]
    use sui::sui::SUI;
    #[test_only]
    use sui::test_scenario::{Self, next_tx, end};
    #[test_only]
    use llp::llp::LLP;
    use admin::admin::{is_admin, Manage};


    const LPP_DECIMAL: u256 = 1000000000;
    const LP_PRICE:    u256 = 1000000000;
    const BASIS_POINTS_DIVISOR: u64 = 10000;

    const ERequireAdminPermission: u64 = 1005;

    struct Vault<phantom P, phantom LLP> has key, store {
        id: UID,
        pool: Coin<P>,
        lp_price: u256,
        lp_supply: u256,
        lp_valult: Coin<LLP>,
        total_fee: u256,
        liquidity_reward_basis_oints:u64,
        staking_reward_basis_points:u64,
        treasury_reward_basis_points:u64,
        host_fee_basis_points:u64,
        vault_fee_basis_points:u64,
        player_fee_basis_points:u64,
        liquidity_rewards:Coin<P>,
        staking_rewards:Coin<P>,
        treasury_rewards:Coin<P>,
        users: VecMap<address, u64>,
    }

    public entry fun create_vault<P, LLP>(lp: Coin<LLP>, ctx: &mut TxContext) {
        public_share_object(Vault<P, LLP> {
            id: object::new(ctx),
            pool: coin::zero<P>(ctx),
            lp_price: (LP_PRICE as u256),
            lp_supply: 0,
            lp_valult: lp,
            total_fee:0,
            liquidity_reward_basis_oints:3000,
            staking_reward_basis_points:5000,
            treasury_reward_basis_points:2000,
            host_fee_basis_points: 500,
            vault_fee_basis_points: 100,
            player_fee_basis_points: 200,
            liquidity_rewards: coin::zero(ctx),
            staking_rewards: coin::zero(ctx),
            treasury_rewards: coin::zero(ctx),
            users: vec_map::empty(),
        })
    }

    public entry fun add_liquidity<P, LLP>(vau: &mut Vault<P, LLP>, c: Coin<P>, ctx: &mut TxContext) {
        let c = collect_vault_fee(vau, c, ctx);

        let value = coin::value(&c);

        let pool_value = coin::value(&vau.pool);
        coin::join(&mut vau.pool, c);

        let amt = (pool_value as u256) * (vau.lp_price as u256) / (LPP_DECIMAL as u256);
        let llp_supply = vau.lp_supply;
        let lp = (value as u256) * (vau.lp_price as u256) / (LPP_DECIMAL as u256);

        let mint:u256;
        if (amt == 0) {
            mint = lp;
        } else {
            mint = lp * llp_supply / amt;
        };

        vau.lp_supply = vau.lp_supply + mint;
        let give = coin::split(&mut vau.lp_valult, (mint as u64), ctx);
        public_transfer(give, tx_context::sender(ctx));
    }

    public entry fun remove_liquidity<P, LLP>(vau: &mut Vault<P, LLP>, c: Coin<LLP>, ctx: &mut TxContext) {
        let value = coin::value(&c);
        let pool_value = coin::value(&vau.pool);
        let amt = (pool_value as u256) * (LP_PRICE as u256) / (LPP_DECIMAL as u256);
        let ret = (value as u256) * amt / vau.lp_supply;

        vau.lp_supply = vau.lp_supply - (value as u256);
        coin::join(&mut vau.lp_valult, c);

        let give = coin::split(&mut vau.pool, (ret as u64), ctx);
        let give = collect_vault_fee(vau, give, ctx);
        public_transfer(give, tx_context::sender(ctx))
    }



    public(friend) fun win<P, LLP>(vau: &mut Vault<P, LLP>, c: Coin<P>) {
        let value = coin::value(&c);
        let pool_value = coin::value(&vau.pool);
        let amount:u256 = (value as u256) * vau.lp_price / (LPP_DECIMAL as u256);

        let new_amount = (pool_value as u256) + amount;
        let lp_price = new_amount * (LPP_DECIMAL as u256) / (pool_value as u256);
        vau.lp_price = lp_price;

        coin::join(&mut vau.pool, c);
    }

    public(friend) fun take_bet<P, LLP>(vau: &mut Vault<P, LLP>, c: Coin<P>) {
        let value = coin::value(&c);
        let pool_value = coin::value(&vau.pool);
        let amount:u256 = (value as u256) * (vau.lp_price as u256)  / (LPP_DECIMAL as u256);

        let new_amount = (pool_value as u256 ) + amount;
        let lp_price = new_amount * LPP_DECIMAL / (pool_value as u256);
        vau.lp_price = lp_price;

        coin::join(&mut vau.pool, c);
    }

    public(friend) fun return_bet<P, LLP>(vau: &mut Vault<P, LLP>,bet:u64,ctx:&mut TxContext):Coin<P> {
        let pool_value = coin::value(&vau.pool);
        let amount:u256 = (bet as u256)* vau.lp_price   / LPP_DECIMAL;

        let new_amount = (pool_value as u256)  + amount;
        let lp_price = new_amount * LPP_DECIMAL / (pool_value as u256) ;
        vau.lp_price = lp_price;

        let split = coin::split(&mut vau.pool, bet, ctx);
        split
    }

    public(friend) fun lost_multiple_times<P, LLP>(vau: &mut Vault<P, LLP>, c: Coin<P>,mult:u64, ctx: &mut TxContext): Coin<P> {
        assert!(mult > 1, 1101);

        let value = (coin::value(&c) * (mult-1) as u256);
        let pool_value = (coin::value(&vau.pool) as u256);

        let amount:u256 = value * vau.lp_price  / LPP_DECIMAL;

        let new_amount = (pool_value as u256) + amount;
        let lp_price = new_amount * LPP_DECIMAL / pool_value;

        vau.lp_price = lp_price;


        let fee = (value * (vau.host_fee_basis_points as u256) / (BASIS_POINTS_DIVISOR as u256) as u64);

        collect_host_fee(vau, fee, ctx);

        let split = coin::split(&mut vau.pool, (value as u64) - fee, ctx);
        coin::join(&mut c, split);
        c
    }



    public(friend) fun lose<P, LLP>(vau: &mut Vault<P, LLP>, c: Coin<P>, ctx: &mut TxContext): Coin<P> {
        let value = coin::value(&c);
        let pool_value = coin::value(&vau.pool);

        let amount:u256 = (value as u256) * vau.lp_price  / LPP_DECIMAL;

        let new_amount = (pool_value as u256) + amount;
        let lp_price = new_amount * LPP_DECIMAL  / (pool_value as u256);
        vau.lp_price = lp_price;

        let fee = ((value as u256) * (vau.host_fee_basis_points as u256) / (BASIS_POINTS_DIVISOR as u256) as u64);

        collect_host_fee(vau, fee, ctx);

        let split = coin::split(&mut vau.pool, value - fee, ctx);
        coin::join(&mut c, split);
        c
    }

    public(friend) fun lose_amount<P, LLP>(vau: &mut Vault<P, LLP>, c: Coin<P>,value:u64, ctx: &mut TxContext): Coin<P> {
        let pool_value = coin::value(&vau.pool);

        let amount:u256 = (value as u256) * vau.lp_price   / LPP_DECIMAL;

        let new_amount = (pool_value as u256) + amount;
        let lp_price = new_amount * LPP_DECIMAL/ (pool_value as u256);

        vau.lp_price = lp_price;

        let fee = ((value as u256) * (vau.host_fee_basis_points as u256) / (BASIS_POINTS_DIVISOR as u256) as u64);

        collect_host_fee(vau, fee, ctx);

        let split = coin::split(&mut vau.pool, value - fee, ctx);
        coin::join(&mut c, split);
        c
    }

    public fun get_player_fee<P,LLP>(vau: &Vault<P, LLP>) :u64 {
        vau.player_fee_basis_points
    }

    public fun get_vault_fee<P,LLP>(vau: &Vault<P, LLP>) :u64 {
        vau.vault_fee_basis_points
    }

    public fun pool_amount<P,LLP> (vau: &Vault<P, LLP>) :u64 {
        coin::value(&vau.pool)
    }

    public fun check_pool_amount<P,LLP> (vau: &Vault<P, LLP>,amount:u64) :bool {
        (coin::value(&vau.pool) *100/10000) >= amount
    }

    public(friend) fun collect_player_fee<P,LLP>(vau: &mut Vault<P, LLP>,paid:Coin<P>,amount:u64,ctx:&mut TxContext):Coin<P>{
        //let amount = coin::value(&paid);
        let fee = coin::split(&mut paid, amount * vau.player_fee_basis_points / BASIS_POINTS_DIVISOR, ctx);
        collect_fee(vau, fee, ctx);
        paid
    }

    public(friend) fun collect_vault_fee<P,LLP>(vau: &mut Vault<P, LLP>,paid:Coin<P>,ctx:&mut TxContext):Coin<P>{
        let amount = coin::value(&paid);
        let fee = coin::split(&mut paid, amount * vau.vault_fee_basis_points / BASIS_POINTS_DIVISOR, ctx);
        collect_fee(vau, fee, ctx);
        paid
    }

    fun collect_fee<P,LLP>(vau: &mut Vault<P, LLP>,paid:Coin<P>,ctx: &mut TxContext) {
        let fee = coin::value(&paid);
        let liquidity = coin::split(&mut paid, fee * vau.liquidity_reward_basis_oints / BASIS_POINTS_DIVISOR, ctx);
        let staking = coin::split(&mut paid, fee * vau.staking_reward_basis_points / BASIS_POINTS_DIVISOR, ctx);
        let treasury = coin::split(&mut paid, fee * vau.treasury_reward_basis_points / BASIS_POINTS_DIVISOR, ctx);
        coin::join(&mut vau.liquidity_rewards, liquidity);
        coin::join(&mut vau.staking_rewards,staking);
        coin::join(&mut vau.treasury_rewards,treasury);
        // paid at now is zero. for quick join to the treasury
        coin::join(&mut vau.treasury_rewards,paid);
    }

    fun collect_host_fee<P,LLP>(vau: &mut Vault<P, LLP>,fee:u64,ctx: &mut TxContext) {
        vau.total_fee = vau.total_fee + (fee as u256);
        let liquidity = coin::split(&mut vau.pool, fee * vau.liquidity_reward_basis_oints / BASIS_POINTS_DIVISOR, ctx);
        let staking = coin::split(&mut vau.pool, fee * vau.staking_reward_basis_points / BASIS_POINTS_DIVISOR, ctx);
        let treasury = coin::split(&mut vau.pool, fee * vau.treasury_reward_basis_points / BASIS_POINTS_DIVISOR, ctx);
        coin::join(&mut vau.liquidity_rewards, liquidity);
        coin::join(&mut vau.staking_rewards,staking);
        coin::join(&mut vau.treasury_rewards,treasury);
    }

    public(friend) fun take_treasury<P,LLP>(vau: &mut Vault<P, LLP>, treasury: Coin<P>) {
        coin::join(&mut vau.treasury_rewards,treasury);
    }

    public entry fun cliam_treasury<P, LLP>(vau: &mut Vault<P, LLP>,adm: &mut Manage, ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        let amount = coin::value(&vau.treasury_rewards);
        let treasury = coin::split(&mut vau.treasury_rewards, amount, ctx);
        public_transfer(treasury, tx_context::sender(ctx));
    }

    public entry fun claim_staking<P,LLP>(vau: &mut Vault<P, LLP>,adm: &mut Manage, ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        let amount = coin::value(&vau.staking_rewards);
        let staking = coin::split(&mut vau.staking_rewards, amount, ctx);
        public_transfer(staking, tx_context::sender(ctx));
    }

    public entry fun claim_liquidity<P,LLP>(vau: &mut Vault<P, LLP>,adm: &mut Manage, ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        let amount = coin::value(&vau.liquidity_rewards);
        let liquidity = coin::split(&mut vau.liquidity_rewards, amount, ctx);
        public_transfer(liquidity, tx_context::sender(ctx));
    }

    public entry fun change_liquidity_reward_basis_points<P, LLP>(vau: &mut Vault<P, LLP>, adm: &mut Manage, basis_points: u64,ctx:&mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        vau.liquidity_reward_basis_oints = basis_points;
    }

    public entry fun change_staking_reward_basis_points<P, LLP>(vau: &mut Vault<P, LLP>, adm: &mut Manage, basis_points: u64,ctx:&mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        vau.staking_reward_basis_points = basis_points;
    }

    public entry fun change_treasury_reward_basis_points<P, LLP>(vau: &mut Vault<P, LLP>, adm: &mut Manage, basis_points: u64,ctx:&mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        vau.treasury_reward_basis_points = basis_points;
    }

    public entry fun change_host_fee<P,LLP>(vau: &mut Vault<P, LLP>, adm: &mut Manage, basis_points: u64,ctx:&mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        vau.host_fee_basis_points = basis_points;
    }

    public entry fun change_vault_fee<P,LLP>(vau: &mut Vault<P, LLP>, adm: &mut Manage, basis_points: u64,ctx:&mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        vau.vault_fee_basis_points = basis_points;
    }

    public entry fun change_player_fee<P,LLP>(vau: &mut Vault<P, LLP>, adm: &mut Manage, basis_points: u64,ctx:&mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        vau.player_fee_basis_points = basis_points;
    }

    #[test]
    fun test_win() {
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(sender);
        let llp = coin::mint_for_testing<LLP>(1000000000000000, &mut ctx);
        let sui = coin::mint_for_testing<SUI>(1000000000000000, &mut ctx);
        create_vault<SUI, LLP>(llp, &mut ctx);
        next_tx(&mut scenario, sender);
        let vault = test_scenario::take_shared<Vault<SUI, LLP>>(&mut scenario);
        add_liquidity(&mut vault, sui, &mut ctx);
        let bet_amount = coin::mint_for_testing<SUI>(10000000000, &mut ctx);
        win(&mut vault, bet_amount);
        let bet_amount = coin::mint_for_testing<SUI>(1000000000000, &mut ctx);
        win(&mut vault, bet_amount);
        let bet_amount = coin::mint_for_testing<SUI>(10000000000000, &mut ctx);
        let c = lose(&mut vault, bet_amount, &mut ctx);
        coin::burn_for_testing(c);
        let bet_amount = coin::mint_for_testing<SUI>(1000000000000, &mut ctx);
        let c = lose(&mut vault, bet_amount, &mut ctx);
        coin::burn_for_testing(c);
        let bet_amount = coin::mint_for_testing<SUI>(100000000000000, &mut ctx);
        let c = lose(&mut vault, bet_amount, &mut ctx);
        coin::burn_for_testing(c);
        let bet_amount = coin::mint_for_testing<SUI>(100000000000, &mut ctx);
        let c = lose(&mut vault, bet_amount, &mut ctx);

        coin::burn_for_testing(c);

        next_tx(&mut scenario, sender);
        let lp = test_scenario::take_from_sender<Coin<LLP>>(&mut scenario);
        remove_liquidity<SUI, LLP>(&mut vault, lp, &mut ctx);

        next_tx(&mut scenario, sender);

        let acc = test_scenario::take_from_sender<Coin<SUI>>(&mut scenario);
        //let balance = coin::value(&acc);


        coin::burn_for_testing(acc);
        test_scenario::return_shared(vault);
        end(scenario);
    }

    #[test]
    fun test_lost_multiple_times() {
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(sender);
        let llp = coin::mint_for_testing<LLP>(1000000000000000, &mut ctx);
        let sui = coin::mint_for_testing<SUI>(1000000000000000, &mut ctx);
        create_vault<SUI, LLP>(llp, &mut ctx);
        next_tx(&mut scenario, sender);
        let vault = test_scenario::take_shared<Vault<SUI, LLP>>(&mut scenario);
        add_liquidity(&mut vault, sui, &mut ctx);

        let bet_amount = coin::mint_for_testing<SUI>(10000000000000, &mut ctx);
        let c = lose(&mut vault, bet_amount, &mut ctx);
        coin::burn_for_testing(c);
        let bet_amount = coin::mint_for_testing<SUI>(1000000000000, &mut ctx);
        let c = lose(&mut vault, bet_amount, &mut ctx);
        coin::burn_for_testing(c);
        let bet_amount = coin::mint_for_testing<SUI>(100000000000000, &mut ctx);
        let c = lose(&mut vault, bet_amount, &mut ctx);
        coin::burn_for_testing(c);
        let bet_amount = coin::mint_for_testing<SUI>(100000000000, &mut ctx);
        let c = lose(&mut vault, bet_amount, &mut ctx);
        coin::burn_for_testing(c);

        next_tx(&mut scenario, sender);
        let lp = test_scenario::take_from_sender<Coin<LLP>>(&mut scenario);
        remove_liquidity<SUI, LLP>(&mut vault, lp, &mut ctx);

        next_tx(&mut scenario, sender);

        let acc = test_scenario::take_from_sender<Coin<SUI>>(&mut scenario);
        coin::burn_for_testing(acc);
        test_scenario::return_shared(vault);
        end(scenario);
    }
}
