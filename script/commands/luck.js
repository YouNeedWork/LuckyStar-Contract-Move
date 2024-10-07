const fs = require("fs");
const { execSync } = require("child_process");


function luck(){
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
        "sui client publish --json --gas-budget 1000000000 ../luck/"
      ).toString();
      const resultJson = JSON.parse(result);
      const packageObject = resultJson?.effects?.created.find(
        (val) => val?.owner == "Immutable"
      );
      const houseCapObject = resultJson?.effects?.created.find(
        (val) => val?.owner?.AddressOwner == address
      );
      if (
        packageObject.owner === "Immutable" &&
        houseCapObject?.owner?.AddressOwner === address
      ) {
        return packageObject.reference.objectId;
      } else {
        throw "Error!! Invalid artifacts produced from compilation!";
      }
    } catch (e) {
      console.error("Error during publishing", e);
    }
  }

module.exports.luck = luck;