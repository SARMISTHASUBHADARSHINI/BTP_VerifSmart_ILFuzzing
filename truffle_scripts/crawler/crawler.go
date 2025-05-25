package main

import (
	"ilf/data_collect"
	"flag"
	"fmt"
	"os"
	"path"
	// "github.com/h2so5/goback/regexp"
)

var contractListURL = "https://etherscan.io/contractsVerified/"

func Crawl(address string, storePath string) {
	contracts, err := data_collect.BuildContractsByAddress(address)
	if err != nil {
		panic(err)
	}

	mainContract := contracts[0]

	for _, contract := range contracts {
		err = contract.StoreToPath(storePath)
		if err != nil {
			panic(err)
		}
	}

	mainContractsPath := path.Join(storePath, "main_contracts.txt")
	f, err := os.OpenFile(mainContractsPath, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer f.Close()

	_, err = f.WriteString(mainContract.Address + "\n")
	if err != nil {
		fmt.Println(err)
		return
	}

	err = mainContract.StoreInvolvedContracts(storePath, contracts)
	if err != nil {
		panic(err)
	}
}

func main() {
	a := flag.String("address", "", "")
	p := flag.String("output", path.Join(data_collect.UserHomeDir(), "Desktop", "contracts"), "directory to store contract files.")
	flag.Parse()
	Crawl(*a, *p)
}
