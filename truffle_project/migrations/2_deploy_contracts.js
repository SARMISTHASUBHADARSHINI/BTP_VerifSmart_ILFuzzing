const Crowdsale = artifacts.require("Crowdsale");
const HotDollarsToken = artifacts.require("HotDollarsToken");

module.exports = function(deployer) {
  deployer.deploy(Crowdsale);
  deployer.deploy(HotDollarsToken);
}; 