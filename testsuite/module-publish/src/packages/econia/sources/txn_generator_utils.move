module econia::txn_generator_utils {
    use econia::market;
    use econia::incentives;
    use econia::assets::{Self, BC, QC, UC};
    use econia::user;
    use aptos_framework::coin::{Coin, Self};
    use aptos_framework::signer;
    // use aptos_framework::account;

    /// Lot size for pure coin test market.
    const LOT_SIZE_COIN: u64 = 2;
    /// Tick size for pure coin test market.
    const TICK_SIZE_COIN: u64 = 3;
    /// Minimum size for pure coin test market.
    const MIN_SIZE_COIN: u64 = 4;
    /// Underwriter ID for generic test market.
    const UNDERWRITER_ID: u64 = 345;
    /// Custodian ID flag for no custodian.
    const NO_CUSTODIAN: u64 = 0;
    /// Market ID for pure coin test market.
    const MARKET_ID_COIN: u64 = 1;
    /// Flag for ask side.
    const ASK: bool = true;
    /// Flag for bid side.
    const BID: bool = false;
    /// Flag to abort during a self match.
    const ABORT: u8 = 0;
    /// Flag to cancel maker order only during a self match.
    const CANCEL_MAKER: u8 = 2;


    public entry fun register_market(publisher: &signer) {
        market::init_setup(publisher);
        // Get market registration fee.
        let fee = incentives::get_market_registration_fee();
        // // Register publisher coin store.
        // coin::register<APT>(publisher);
        // Register pure coin market.
        market::register_market_base_coin<BC, QC, UC>(
            LOT_SIZE_COIN, TICK_SIZE_COIN, MIN_SIZE_COIN,
            assets::mint(publisher, fee));
    }

    public entry fun register_market_accounts(user: &signer) {
        user::register_market_account<BC, QC>(user, MARKET_ID_COIN, NO_CUSTODIAN);
    }

    public entry fun deposit_coins(user: &signer) {
        user::deposit_coins<QC>(signer::address_of(user), MARKET_ID_COIN, NO_CUSTODIAN, assets::mint<QC>(user, 1000));
        user::deposit_coins<BC>(signer::address_of(user), MARKET_ID_COIN, NO_CUSTODIAN, assets::mint<BC>(user, 1000));
    }
    
    public entry fun place_bid_limit_order(user: &signer, price: u64) {
        market::place_limit_order_user<BC, QC>(user, MARKET_ID_COIN, @econia, BID, 3, price, 2, CANCEL_MAKER);
    }

    public entry fun place_ask_limit_order(user: &signer, price: u64) {
        market::place_limit_order_user<BC, QC>(user, MARKET_ID_COIN, @econia, ASK, 3, price, 2, CANCEL_MAKER);
    }
}
    