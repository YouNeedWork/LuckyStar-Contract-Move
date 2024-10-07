const { program } = require("commander");
const { luck } = require("./commands/luck");
const { all } = require("./commands/all");
const { airdrop } = require("./commands/airdrop");
require("dotenv").config();

program
  .name("luckyStar-deploy-script")
  .description("CLI to Deploy LuckyStar Smart Contracts")
  .version("0.0.1");

program
  .command("Luck")
  .description("Deploy Luck Coin Smart Contracts")
  .action(luck);

program.command("All").description("Deploy All Smart Contracts").action(all);

program
  .command("Airdrop")
  .description("Deploy All Smart Contracts")
  .action(airdrop);

program.parse();
