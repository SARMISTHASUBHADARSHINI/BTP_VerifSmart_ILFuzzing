package main

import (
	"fmt"
	"io/ioutil"
	"os"
	"path"
)

func writeStrToPath(content string, p string) error {
	return ioutil.WriteFile(p, []byte(content), 0644)
}

func main() {
	// Create the project directory
	projectPath := "truffle_project"
	if err := os.MkdirAll(projectPath, os.ModePerm); err != nil {
		fmt.Printf("Error creating project directory: %v\n", err)
		return
	}

	// Create the contract directory
	contractPath := path.Join(projectPath, "contracts")
	if err := os.MkdirAll(contractPath, os.ModePerm); err != nil {
		fmt.Printf("Error creating contracts directory: %v\n", err)
		return
	}

	// Create the migrations directory
	migrationsPath := path.Join(projectPath, "migrations")
	if err := os.MkdirAll(migrationsPath, os.ModePerm); err != nil {
		fmt.Printf("Error creating migrations directory: %v\n", err)
		return
	}

	// Create truffle-config.js
	truffleConfig := `module.exports = {
  networks: {
    development: {
      host: "127.0.0.1",
      port: 8545,
      network_id: "*",
      gas: 1000000000
    }
  },
  compilers: {
     solc: {
       version: "native",
       optimizer: {
         enabled: true,
         runs: 200
       }
     }
  }
};`
	if err := writeStrToPath(truffleConfig, path.Join(projectPath, "truffle-config.js")); err != nil {
		fmt.Printf("Error creating truffle-config.js: %v\n", err)
		return
	}

	// Create Migrations.sol
	migrationsContract := `pragma solidity ^0.4.23;

contract Migrations {
  address public owner;
  uint public last_completed_migration;

  constructor() public {
    owner = msg.sender;
  }

  modifier restricted() {
    if (msg.sender == owner) _;
  }

  function setCompleted(uint completed) public restricted {
    last_completed_migration = completed;
  }

  function upgrade(address new_address) public restricted {
    Migrations upgraded = Migrations(new_address);
    upgraded.setCompleted(last_completed_migration);
  }
}`
	if err := writeStrToPath(migrationsContract, path.Join(contractPath, "Migrations.sol")); err != nil {
		fmt.Printf("Error creating Migrations.sol: %v\n", err)
		return
	}

	// Create crowdsale.sol
	crowdsaleContent := `contract Crowdsale { function echidna_alwaystrue() public returns (bool) { return(true); }
  uint256 goal = 10000 * 10**18;
  uint256 raised = 0;
  uint256 closeTime;  
  address owner; 
  mapping(address => uint256) deposits;
  uint256 phase; // 0: active, 1: success, 2: refund

  constructor() public {
    closeTime = now + 30 days;
    owner = msg.sender;
  }

  function invest() public payable {
    require(phase == 0 && raised < goal);
    deposits[msg.sender] += msg.value;  
    raised += msg.value; 
  }

  function setPhase(uint256 newPhase) public {
    require((newPhase == 1 && raised >= goal) ||
            (newPhase == 2 && raised < goal
              && now >= closeTime));
    phase = newPhase;
  }
  
  function setOwner(address newOwner) public {
    // require(msg.sender == owner);
    owner = newOwner;  
  }

  function withdraw() public {
    require(phase == 1);
    owner.transfer(raised);
  }

  function refund() public {
    require(phase == 2);
    msg.sender.transfer(deposits[msg.sender]);
    deposits[msg.sender] = 0;
  }
}`
	if err := writeStrToPath(crowdsaleContent, path.Join(contractPath, "crowdsale.sol")); err != nil {
		fmt.Printf("Error creating crowdsale.sol: %v\n", err)
		return
	}

	// Create initial migration script
	initialMigration := `var Migrations = artifacts.require("./Migrations.sol");

module.exports = function(deployer) {
  deployer.deploy(Migrations);
};`
	if err := writeStrToPath(initialMigration, path.Join(migrationsPath, "1_initial_migration.js")); err != nil {
		fmt.Printf("Error creating 1_initial_migration.js: %v\n", err)
		return
	}

	// Create deploy contracts script
	deployScript := `var Crowdsale = artifacts.require("./crowdsale.sol");

module.exports = function(deployer) {
  deployer.deploy(Crowdsale);
};`
	if err := writeStrToPath(deployScript, path.Join(migrationsPath, "2_deploy_contracts.js")); err != nil {
		fmt.Printf("Error creating 2_deploy_contracts.js: %v\n", err)
		return
	}

	// Create main_contracts.txt
	if err := writeStrToPath("Crowdsale", path.Join(projectPath, "main_contracts.txt")); err != nil {
		fmt.Printf("Error creating main_contracts.txt: %v\n", err)
		return
	}

	fmt.Println("Project setup completed successfully!")
} 