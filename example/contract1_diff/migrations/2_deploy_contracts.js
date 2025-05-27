const CareerOnToken = artifacts.require("CareerOnToken");
 
module.exports = function(deployer) {
  // Deploy with initial amount of 100000000000000000 tokens and 18 decimals
  deployer.deploy(CareerOnToken, "100000000000000000", 18);
}; 