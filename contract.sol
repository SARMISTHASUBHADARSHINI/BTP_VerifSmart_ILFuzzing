// SPDX-License-Identifier: MIT
pragma solidity ^0.4.25;

contract Crowdsale {
    address public owner;
    uint256 public rate = 100;
    uint256 public raisedAmount;

    mapping(address => uint256) public balances;

    constructor() public {
        owner = msg.sender;
    }

    function buyTokens() public payable {
        require(msg.value > 0, "Send ETH to buy tokens");
        uint256 tokens = msg.value * rate;
        balances[msg.sender] += tokens;
        raisedAmount += msg.value;
    }

    function withdrawFunds(uint256 amount) public {
        require(msg.sender == owner, "Only owner can withdraw");
        require(amount <= address(this).balance, "Insufficient funds");
        owner.transfer(amount);
    }

    function changeRate(uint256 newRate) public {
        require(msg.sender == owner, "Only owner can change rate");
        rate = newRate;
    }

    function getBalance() public view returns (uint256) {
        return balances[msg.sender];
    }
}
