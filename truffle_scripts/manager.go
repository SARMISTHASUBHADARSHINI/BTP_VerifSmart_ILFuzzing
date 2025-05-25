package data_collect

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io/ioutil"
	"os"
	"path"
	"strings"
)

var truffleJSString = `module.exports = {
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
};
`

var migrationContractString = `pragma solidity ^0.4.23;

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
}
`

var migrationScriptString = `var Migrations = artifacts.require("./Migrations.sol");

module.exports = function(deployer) {
  deployer.deploy(Migrations);
};
`

type ContractManager struct {
	ContractsPath string
	ContractsMap  map[string]*VerifiedContract
	MainContracts map[string]bool
}

func LoadContractsFromPath(p string) (*ContractManager, error) {
	if exists, _ := Exists(p); !exists {
		err := fmt.Errorf("Path %s does not exist", p)
		return nil, err
	}

	files, err := ioutil.ReadDir(p)
	if err != nil {
		return nil, err
	}

	contractManager := &ContractManager{
		ContractsPath: p,
		ContractsMap:  make(map[string]*VerifiedContract),
		MainContracts: make(map[string]bool)}

	for _, f := range files {
		if f.IsDir() {
			contractPath := path.Join(p, f.Name())
			c, err := VerifiedContractFromPath(contractPath)
			if err != nil {
				return nil, err
			}
			c.Manager = contractManager
			contractManager.ContractsMap[c.Address] = c
			// contractManager.MainContracts[c.Address] = true
		}
	}

	file, err := os.Open(path.Join(p, "main_contracts.txt"))
	if err != nil {
		return nil, err
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := scanner.Text()
		if line != "" {
			contractManager.MainContracts[line] = true
		}
	}

	if err := scanner.Err(); err != nil {
		return nil, err
	}

	return contractManager, nil
}

func (m *ContractManager) MakeTruffleProject(p string) error {
	deploys := make(map[string]*Deploy)
	loadedAddrs := make(map[string]bool)

	for address := range m.MainContracts {
		if c, ok := m.ContractsMap[address]; ok {
			if _, ok := loadedAddrs[address]; !ok {
				deploy, err := c.ToDeploy()
				if err != nil {
					return err
				}
				deploys[address] = deploy
				loadedAddrs[address] = true
			}
		} else {
			err := fmt.Errorf("there is no contract %s", address)
			return err
		}
	}

	varCodeMap := make(map[string]string)
	deployCodeMap := make(map[string]string)
	for address, deploy := range deploys {
		if c, ok := m.ContractsMap[address]; ok {
			err := deploy.AssignVarToContract(make(map[string]int), c, m)
			if err != nil {
				return err
			}

			varCode := deploy.ToJSVarCode()
			varCodeMap[address] = varCode

			deployCode, err := deploy.ToJSDeployCode(m)
			if err != nil {
				return err
			}
			deployCodeMap[address] = deployCode
		}
	}

	var contracts []string

	for address, deploy := range deploys {
		c, _ := m.ContractsMap[address]
		// contracts = append(contracts, fmt.Sprintf("%s %s", c.Address, c.Name))
		contracts = append(contracts, address)
		varCode, _ := varCodeMap[address]
		deployCode, _ := deployCodeMap[address]
		comment := fmt.Sprintf("// %s %s %v", c.Address, c.Name, c.TheABI.Constructor)
		jscode := comment + "\n" + varCode + "\n" + deployCode

		trufflePath := path.Join(p, address, "truffle")

		err := DeleteAndMkdir(trufflePath)
		if err != nil {
			return err
		}

		contractsTrufflePath := path.Join(trufflePath, "contracts")
		err = DeleteAndMkdir(contractsTrufflePath)
		if err != nil {
			return err
		}
		err = WriteStrToPath(migrationContractString, path.Join(contractsTrufflePath, "Migrations.sol"))
		if err != nil {
			return err
		}

		migrationsTrufflePath := path.Join(trufflePath, "migrations")
		err = DeleteAndMkdir(migrationsTrufflePath)
		if err != nil {
			return err
		}
		err = WriteStrToPath(migrationScriptString, path.Join(migrationsTrufflePath, "1_initial_migration.js"))
		if err != nil {
			return err
		}

		testTrufflePath := path.Join(trufflePath, "test")
		err = DeleteAndMkdir(testTrufflePath)
		if err != nil {
			return err
		}

		// pwd, err := os.Getwd()
		// if err != nil {
		// 	return err
		// }

		// err = os.Chdir(trufflePath)
		// if err != nil {
		// 	return err
		// }

		// cmd := exec.Command("truffle", "init")
		// err = cmd.Run()
		// if err != nil {
		// 	return err
		// }

		// err = os.Chdir(pwd)
		// if err != nil {
		// 	return err
		// }

		for _, node := range deploy.PostOrderContracts {
			c, err := node.ToContract(m)
			targetPath := path.Join(trufflePath, "contracts", fmt.Sprintf("%s.sol", c.ID))
			if exists, _ := Exists(targetPath); !exists {
				err = CopyFile(c.SourceNormalized, targetPath)
				if err != nil {
					return err
				}
			}
		}

		err = WriteStrToPath(jscode, path.Join(trufflePath, "migrations", "2_deploy_contracts.js"))
		if err != nil {
			return err
		}

		// err = WriteStrToPath(truffleJSString, path.Join(trufflePath, "truffle.js"))
		// if err != nil {
		// 	return err
		// }

		err = WriteStrToPath(truffleJSString, path.Join(trufflePath, "truffle-config.js"))
		if err != nil {
			return err
		}

		info := ContractInfo{
			Address:      c.Address,
			Name:         c.Name,
			ID:           c.ID,
			OptEnabled:   c.OptEnabled,
			CompilerText: c.CompilerText,
			Runs:         c.Runs}

		infoJSON, err := json.Marshal(&info)

		infoPath := path.Join(p, address, "info.json")
		err = WriteStrToPath(string(infoJSON), infoPath)
		if err != nil {
			return err
		}
	}

	err := WriteStrToPath(strings.Join(contracts, "\n")+"\n", path.Join(p, "contracts.txt"))
	if err != nil {
		return err
	}

	return nil
}
