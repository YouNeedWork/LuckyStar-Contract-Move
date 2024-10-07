const fs = require("fs");
const { execSync } = require("child_process");

function airdrop() {
  setAddressAsCurrent(process.env.ADDRESS);
  airdrop(process.env.ADDRESS);
}

function setAddressAsCurrent(address) {
  const activeAddress = execSync("sui client active-address").toString();
  if (activeAddress !== address) {
    execSync(`sui client switch --address ${address}`);
  }
}

function airdrop(address) {
  try {
    let publish = JSON.parse(fs.readFileSync("publish.json"));
    //sui client call --package $PKG --module airdrop --function create --type-args $PKG::luck::LUCK --args [0x7a5a0c202a1cf2e9200ca97efdee7291b8f00e2db2a42121bf6a04b830908b1e] 120000000000000000 --gas-budget 1000000000
    const result = execSync(
      `sui client call --json --gas-budget 500000000 --package ${publish["packageId"]} --module airdrop --function create  --type-args ${publish["luckType"]} --args [${publish["luckId"]}] 50000000000000000`
    ).toString();
    const resultJson = JSON.parse(result);
    console.log(resultJson);

    let re = execSync(
      `sui client call --json --gas-budget 500000000 --package ${publish["packageId"]} --module airdrop --function create  --type-args ${publish["suiType"]} --args [${publish["suiId"]}] 50000000000000000`
    ).toString();
    const rejson = JSON.parse(re);
    console.log(rejson);

    const result0 = execSync(
      `sui client call --json --gas-budget 500000000 --package ${publish["packageId"]} --module airdrop --function create_non_transfer_coin  --type-args ${publish["esLuckType"]} --args ${publish["esluckId"]}`
    ).toString();
    const resultJson0 = JSON.parse(result0);
    console.log(resultJson0);

    const result1 = execSync(
      `sui client call --json --gas-budget 500000000 --package ${publish["packageId"]} --module airdrop --function create_non_transfer_coin  --type-args ${publish["xLuckType"]} --args ${publish["xluckId"]}`
    ).toString();
    const resultJson1 = JSON.parse(result1);
    console.log(resultJson1);
  } catch (e) {
    console.error("Error during publishing", e);
  }
}

module.exports.airdrop = airdrop;
