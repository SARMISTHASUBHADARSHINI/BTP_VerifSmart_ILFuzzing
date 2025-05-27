const YFT = artifacts.require("YFT");
const Ownable = artifacts.require("Ownable");

module.exports = function(deployer) {
  deployer.deploy(YFT, 1000000, "Your First Token", "YFT");  // 1M tokens, name, symbol
  deployer.deploy(Ownable);
}; 