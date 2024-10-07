const fs = require("fs");
const { execSync } = require("child_process");

function all() {
  setAddressAsCurrent(process.env.ADDRESS);
  const packageId = publish(process.env.ADDRESS);
  console.log(packageId);
}

function setAddressAsCurrent(address) {
  const activeAddress = execSync("sui client active-address").toString();
  if (activeAddress !== address) {
    execSync(`sui client switch --address ${address}`);
  }
}

function publish(address) {
  try {
    const result = execSync(
      "sui client publish --json --gas-budget 500000000 ../games/ --with-unpublished-dependencies"
    ).toString();
    const resultJson = JSON.parse(result);
    let packageId = resultJson?.objectChanges?.find(
      (val) => val?.type == "published"
    );

    let data_store = {};
    data_store["packageId"] = packageId.packageId;

    data_store["manageType"] = `${data_store["packageId"]}::admin::Manage`;
    data_store["luckType"] = `${data_store["packageId"]}::luck::LUCK`;
    data_store["esLuckType"] = `${data_store["packageId"]}::esLuck::ESLUCK`;
    data_store["xLuckType"] = `${data_store["packageId"]}::xLuck::XLUCK`;
    data_store["llpType"] = `${data_store["packageId"]}::llp::LLP`;
    data_store["suiType"] = `${data_store["packageId"]}::sui::SUI`;

    let manage = resultJson?.objectChanges?.find(
      (val) =>
        val?.type == "created" && val?.objectType == data_store["manageType"]
    );
    data_store["manageId"] = manage.objectId;
    let luck = resultJson?.objectChanges?.find(
      (val) =>
        val?.type == "created" &&
        val?.objectType ==
          `0x0000000000000000000000000000000000000000000000000000000000000002::coin::Coin<${data_store["luckType"]}>`
    );
    data_store["luckId"] = luck.objectId;

    let sui = resultJson?.objectChanges?.find(
      (val) =>
        val?.type == "created" &&
        val?.objectType ==
          `0x0000000000000000000000000000000000000000000000000000000000000002::coin::Coin<${data_store["suiType"]}>`
    );
    data_store["suiId"] = sui.objectId;

    let llp = resultJson?.objectChanges?.find(
      (val) =>
        val?.type == "created" &&
        val?.objectType ==
          `0x0000000000000000000000000000000000000000000000000000000000000002::coin::Coin<${data_store["llpType"]}>`
    );
    data_store["llpId"] = llp.objectId;

    let xluck = resultJson?.objectChanges?.find(
      (val) =>
        val?.type == "created" &&
        val?.objectType ==
          `${data_store["packageId"]}::nonTransferCoin::NonTransferCoin<${data_store["xLuckType"]}>`
    );
    data_store["xluckId"] = xluck.objectId;

    let esluck = resultJson?.objectChanges?.find(
      (val) =>
        val?.type == "created" &&
        val?.objectType ==
          `${data_store["packageId"]}::nonTransferCoin::NonTransferCoin<${data_store["esLuckType"]}>`
    );
    data_store["esluckId"] = esluck.objectId;
    let string = JSON.stringify(data_store, null, 2);

    fs.writeFile("publish.json", string, function () {});

    console.log(data_store);
  } catch (e) {
    console.error("Error during publishing", e);
  }
}

module.exports.all = all;
