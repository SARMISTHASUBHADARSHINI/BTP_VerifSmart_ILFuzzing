package main

import (
	"ilf/data_collect"
	"flag"
	"fmt"
	"os"
	"path"
)

func main() {
	inp := flag.String("input", path.Join(data_collect.UserHomeDir(), "Desktop", "contracts"), "directory where contract files are stored")
	out := flag.String("output", path.Join(data_collect.UserHomeDir(), "Desktop", "truffle"), "directory to store the output truffle project")
	flag.Parse()

	manager, err := data_collect.LoadContractsFromPath(*inp)
	if err != nil {
		fmt.Println(err)
		os.Exit(2)
	}

	err = manager.MakeTruffleProject(*out)
	if err != nil {
		fmt.Println(err)
		os.Exit(2)
	}
}
