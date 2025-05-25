package data_collect

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"net/http"
	"os"
	"path"
	"reflect"
	"regexp"
	"strings"
	"time"

	"github.com/PuerkitoBio/goquery"

	"github.com/ethereum/go-ethereum/accounts/abi"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/compiler"
	// "github.com/h2so5/goback/regexp"
)

var contractCodeURLBase = "https://etherscan.io/address/%s#code"

type VerifiedContract struct {
	Address             string
	Name                string
	ID                  string
	OptEnabled          bool
	CompilerText        string
	Runs                string
	SourceOriginal      string
	SourceNormalized    string
	TheABI              abi.ABI
	TheABIText          string
	ConstructorArgs     []interface{}
	ConstructorArgsText string
	Manager             *ContractManager
}

type ContractInfo struct {
	Address      string
	Name         string
	ID           string
	OptEnabled   bool
	CompilerText string
	Runs         string
}

func (c *VerifiedContract) StoreInvolvedContracts(p string, contracts []*VerifiedContract) error {
	p = path.Join(p, c.Address, "involved.txt")

	var ids []string

	for _, contract := range contracts {
		ids = append(ids, contract.ID)
	}

	err := WriteStrToPath(strings.Join(ids, "\n"), p)
	if err != nil {
		return err
	}

	return nil
}

func (c *VerifiedContract) StoreToPath(p string) error {
	err := MkdirIfNotExist(p)
	if err != nil {
		return err
	}

	p = path.Join(p, c.Address)

	err = DeleteAndMkdir(p)
	if err != nil {
		return err
	}

	os.MkdirAll(p, os.ModePerm)

	info := ContractInfo{
		Address:      c.Address,
		Name:         c.Name,
		ID:           c.ID,
		OptEnabled:   c.OptEnabled,
		CompilerText: c.CompilerText,
		Runs:         c.Runs}

	infoJSON, err := json.Marshal(&info)

	infoPath := path.Join(p, "info.json")
	err = WriteStrToPath(string(infoJSON), infoPath)
	if err != nil {
		return err
	}

	sourceOriginalPath := path.Join(p, "source_original.sol")
	err = WriteStrToPath(c.SourceOriginal, sourceOriginalPath)
	if err != nil {
		return err
	}

	sourceNormalizedPath := path.Join(p, "source_normalized.sol")
	err = WriteStrToPath(c.SourceNormalized, sourceNormalizedPath)
	if err != nil {
		return err
	}

	abiPath := path.Join(p, "abi.txt")
	err = WriteStrToPath(c.TheABIText, abiPath)
	if err != nil {
		return err
	}

	if c.ConstructorArgsText != "" {
		argsPath := path.Join(p, "constructor_args.txt")
		err = WriteStrToPath(c.ConstructorArgsText, argsPath)
		if err != nil {
			return err
		}
	}

	return nil
}

func VerifiedContractFromPath(p string) (*VerifiedContract, error) {
	infoPath := path.Join(p, "info.json")
	infoBytes, err := ioutil.ReadFile(infoPath)
	if err != nil {
		return nil, err
	}
	var info ContractInfo
	json.Unmarshal(infoBytes, &info)

	sourceOriginalPath := path.Join(p, "source_original.sol")
	if exists, _ := Exists(sourceOriginalPath); !exists {
		err = fmt.Errorf("%s does not exist", sourceOriginalPath)
		return nil, err
	}

	sourceNormalizedPath := path.Join(p, "source_normalized.sol")
	if exists, _ := Exists(sourceNormalizedPath); !exists {
		err = fmt.Errorf("%s does not exist", sourceNormalizedPath)
		return nil, err
	}

	abiPath := path.Join(p, "abi.txt")
	abiFile, err := os.Open(abiPath)
	if err != nil {
		return nil, err
	}
	defer abiFile.Close()
	theABI, err := abi.JSON(abiFile)
	if err != nil {
		return nil, err
	}
	theABIBytes, err := ioutil.ReadFile(abiPath)
	if err != nil {
		return nil, err
	}
	theABIText := string(theABIBytes)

	argsPath := path.Join(p, "constructor_args.txt")
	argsExists, _ := Exists(argsPath)
	inputLenZero := len(theABI.Constructor.Inputs) == 0

	constructorArgs := make([]interface{}, len(theABI.Constructor.Inputs))
	constructorArgsText := ""

	if argsExists && !inputLenZero {
		constructorArgsBytes, err := ioutil.ReadFile(argsPath)
		if err != nil {
			return nil, err
		}
		constructorArgsText = string(constructorArgsBytes)
		err = theABI.Constructor.Inputs.Unpack(&constructorArgs, common.Hex2Bytes(constructorArgsText))
	} else if !argsExists && inputLenZero {

	} else if argsExists && inputLenZero {
		err = fmt.Errorf("%s exists but there is no argument in the ABI %s", argsPath, abiPath)
		return nil, err
	} else {
		err = fmt.Errorf("%s does not exist but there are arguments in the ABI %s", argsPath, abiPath)
		return nil, err
	}

	return &VerifiedContract{
		Address:             info.Address,
		Name:                info.Name,
		ID:                  info.ID,
		OptEnabled:          info.OptEnabled,
		CompilerText:        info.CompilerText,
		Runs:                info.Runs,
		SourceOriginal:      sourceOriginalPath,
		SourceNormalized:    sourceNormalizedPath,
		TheABI:              theABI,
		TheABIText:          theABIText,
		ConstructorArgs:     constructorArgs,
		ConstructorArgsText: constructorArgsText}, nil
}

// VerifiedContractFromAddress takes the address of a contract and a boolean flag indicating whether the contract has contructor arguments
// outpus a VerifiedContract struct
func VerifiedContractFromAddress(address string) (*VerifiedContract, error) {
	address = strings.ToLower(address)

	time.Sleep(250 * time.Millisecond)
	link := fmt.Sprintf(contractCodeURLBase, address)
	res, err := http.Get(link)
	if err != nil {
		return nil, err
	}
	defer res.Body.Close()

	if res.StatusCode != 200 {
		err = fmt.Errorf("status code error: %d %s", res.StatusCode, res.Status)
		return nil, err
	}

	doc, err := goquery.NewDocumentFromReader(res.Body)
	if err != nil {
		return nil, err
	}

	// name := doc.Find("#ContentPlaceHolder1_contractCodeDiv").Find(".table").Eq(0).Find("tr").Eq(0).Find("td").Eq(1).Text()
	name := doc.Find("#ContentPlaceHolder1_contractCodeDiv").Children().Eq(2).Children().Eq(0).Find(".row").Eq(0).Children().Eq(1).Text()
	name = strings.TrimSpace(name)
	optEnabledText := doc.Find("#ContentPlaceHolder1_contractCodeDiv").Children().Eq(2).Children().Eq(1).Find(".row").Eq(0).Children().Eq(1).Text()
	optEnabledText = strings.TrimSpace(optEnabledText)
	optEnabled := false
	if optEnabledText == "Yes" {
		optEnabled = true
	}
	compilerText := doc.Find("#ContentPlaceHolder1_contractCodeDiv").Children().Eq(2).Children().Eq(0).Find(".row").Eq(1).Children().Eq(1).Text()
	compilerText = strings.TrimSpace(compilerText)
	runs := doc.Find("#ContentPlaceHolder1_contractCodeDiv").Children().Eq(2).Children().Eq(1).Find(".row").Eq(1).Children().Eq(1).Text()
	runs = strings.TrimSpace(runs)

	id := fmt.Sprintf("%s_%s", name, address)

	source := doc.Find("#dividcode").Find(".js-sourcecopyarea").Text()
	// source, err := doc.Find("#dividcode").Find(".js-sourcecopyarea").Html()
	// if err != nil {
	// 	return nil, err
	// }

	if len(strings.TrimSpace(source)) == 0 {
		err = fmt.Errorf("contract not verified")
		return nil, err
	}

	// source = strings.Replace(source, "&gt;", ">", -1)
	// source = strings.Replace(source, "&lt;", "<", -1)

	sourceOriginal := source
	sourceNormalized := source

	sourceNormalized = AddUpToVersion(sourceNormalized)

	contractsMap, err := compiler.CompileSolidityString("solc", sourceNormalized)
	if err != nil {
		return nil, err
	}

	// TODO: more accurate replacement
	// for adapting bytes32 type
	for contractName := range contractsMap {
		name := contractName[8:]
		// re := regexp.MustCompile(`\b(?<!")` + name + `(?!")\b`)
		re := regexp.MustCompile(`\b` + name + `\b`)
		newName := fmt.Sprintf("%s_%s", name, address)
		sourceNormalized = re.ReplaceAllString(sourceNormalized, newName)

		re = regexp.MustCompile(`\b"` + newName + `"\b`)
		sourceNormalized = re.ReplaceAllString(sourceNormalized, `"`+name+`"`)
	}

	theABIText := doc.Find("#dividcode").Find("#js-copytextarea2").Text()
	theABIText = strings.TrimSpace(theABIText)
	if len(theABIText) == 0 {
		err = fmt.Errorf("contract not verified")
		return nil, err
	}
	theABI, err := abi.JSON(strings.NewReader(theABIText))
	if err != nil {
		return nil, err
	}

	constructorArgs := make([]interface{}, len(theABI.Constructor.Inputs))
	constructorArgsText := doc.Find("#dividcode").Find(".wordwrap").Eq(2).Text()
	constructorArgsText = strings.TrimSpace(constructorArgsText)

	encodedText := "-----Encoded"
	containsEncoded := strings.Contains(constructorArgsText, encodedText)
	inputLenZero := len(theABI.Constructor.Inputs) == 0

	if !inputLenZero && containsEncoded {
		encodedIndex := strings.Index(constructorArgsText, encodedText)
		constructorArgsText = constructorArgsText[:encodedIndex]

		err = theABI.Constructor.Inputs.Unpack(&constructorArgs, common.Hex2Bytes(constructorArgsText))
		if err != nil {
			return nil, err
		}
	} else if inputLenZero && !containsEncoded {
		constructorArgsText = ""
	} else if !containsEncoded && !inputLenZero {
		err = fmt.Errorf("The constructor of %s has non-zero number of arguments but contains no encoded text in EtherScan", address)
		return nil, err
	} else {
		err = fmt.Errorf("The constructor of %s has zero number of arguments but contains encoded text in EtherScan", address)
		return nil, err
	}

	return &VerifiedContract{
		Address:             address,
		Name:                name,
		ID:                  id,
		OptEnabled:          optEnabled,
		CompilerText:        compilerText,
		Runs:                runs,
		SourceOriginal:      sourceOriginal,
		SourceNormalized:    sourceNormalized,
		TheABI:              theABI,
		TheABIText:          theABIText,
		ConstructorArgs:     constructorArgs,
		ConstructorArgsText: constructorArgsText}, nil
}

func IsAddressContract(address string) (bool, error) {
	address = strings.ToLower(address)

	res, err := http.Get(fmt.Sprintf(contractCodeURLBase, address))
	if err != nil {
		return false, err
	}
	defer res.Body.Close()

	if res.StatusCode != 200 {
		err = fmt.Errorf("status code error: %d %s", res.StatusCode, res.Status)
		return false, err
	}

	doc, err := goquery.NewDocumentFromReader(res.Body)
	if err != nil {
		return false, err
	}

	text := doc.Find("h1.h4").Text()
	if strings.Contains(text, "Contract") {
		return true, nil
	} else {
		return false, nil
	}
}

func HandleType(argType abi.Type, crawledContracts map[string]bool, argVals ...interface{}) ([]*VerifiedContract, error) {
	var contracts []*VerifiedContract

	if argType.T == abi.AddressTy {
		for _, argVal := range argVals {
			if addrVal, ok := argVal.(common.Address); ok {
				address := strings.ToLower(addrVal.Hex())
				if isContract, _ := IsAddressContract(address); isContract {
					newContracts, err := VerifiedContractDepFromAddress(address, crawledContracts)
					if err != nil {
						return nil, err
					}
					if newContracts != nil {
						contracts = append(contracts, newContracts...)
					}
				}
			} else {
				err := fmt.Errorf("cannot cast to common.Address type")
				return nil, err
			}
		}
	} else if argType.T == abi.ArrayTy {
		if argType.Elem != nil {
			for _, argVal := range argVals {
				s := reflect.ValueOf(argVal)
				for i := 0; i < s.Len(); i++ {
					sval := s.Index(i).Interface()
					newContracts, err := HandleType(*(argType.Elem), crawledContracts, sval)
					if err != nil {
						return nil, err
					}
					if newContracts != nil {
						contracts = append(contracts, newContracts...)
					}
				}
			}
		} else {
			err := fmt.Errorf("array type has no elem type")
			return nil, err
		}
	} else {
		return nil, nil
	}

	return contracts, nil
}

// VerifiedContractDepFromAddress takes the address of a contract and a boolean flag indicating whether the contract has contructor arguments
// outputs a list of the contract and the ones that it is dependent on
func VerifiedContractDepFromAddress(address string, crawledContracts map[string]bool) ([]*VerifiedContract, error) {
	address = strings.ToLower(address)

	var contracts []*VerifiedContract

	if _, ok := crawledContracts[address]; !ok {
		c, err := VerifiedContractFromAddress(address)
		if err != nil {
			return nil, err
		}
		crawledContracts[address] = true
		contracts = append(contracts, c)

		lenConstructorABI := len(c.TheABI.Constructor.Inputs)
		lenConstructorArgs := len(c.ConstructorArgs)

		if lenConstructorABI != lenConstructorArgs {
			err = fmt.Errorf("length of constructor ABI is not equal to length of arguments for contract %s", address)
			return nil, err
		}

		for i := 0; i < lenConstructorABI; i++ {
			argAbi := c.TheABI.Constructor.Inputs[i]
			argType := argAbi.Type
			argVal := c.ConstructorArgs[i]
			newContracts, err := HandleType(argType, crawledContracts, argVal)
			if err != nil {
				return nil, err
			}
			if newContracts != nil {
				contracts = append(contracts, newContracts...)
			}
		}
		// fmt.Printf("[%s] [%v] [%s]\n", c.Name, c.TheABI.Constructor, c.Address)
		// fmt.Println(len(contracts))

	}

	return contracts, nil
}

func BuildContractsByAddress(address string) ([]*VerifiedContract, error) {
	address = strings.ToLower(address)
	return VerifiedContractDepFromAddress(address, make(map[string]bool))
}

func (c *VerifiedContract) ToDeploy() (*Deploy, error) {
	// if c.Address == "0xb85a54944b58342b07887942e6f530f616479efd" {
	// 	for i := 0; i < len(c.TheABI.Constructor.Inputs); i++ {
	// 		arg := c.ConstructorArgs[i]
	// 		argABI := c.TheABI.Constructor.Inputs[i]
	// 		if addrArg, ok := arg.(common.Address); ok {
	// 			address := strings.ToLower(addrArg.Hex())
	// 			fmt.Printf("%d %v %v\n", i, argABI.Type.StringKind, address)
	// 		} else {
	// 			fmt.Printf("%d %v %v\n", i, argABI.Type.StringKind, arg)
	// 		}
	// 	}
	// 	fmt.Printf("args: %v\n", c.ConstructorArgs)
	// }

	root, err := ContractToDeployTree(c, make(map[string]*DeployTree))
	if err != nil {
		return nil, err
	}
	root.Father = root

	contracts, err := root.PostOrderTraversal(make(map[string]bool), c.Manager)
	if err != nil {
		return nil, err
	}

	return &Deploy{
		Tree:               root,
		PostOrderContracts: contracts}, nil
}

func ContractToDeployTree(v interface{}, contractsDone map[string]*DeployTree) (*DeployTree, error) {
	node := &DeployTree{}
	if c, ok := v.(*VerifiedContract); ok {
		// node.Value = fmt.Sprintf("%s_%s", c.Name, mainContract.Address)
		node.Value = c.Address
		node.IsContract = true
		contractsDone[c.Address] = node

		for i := 0; i < len(c.TheABI.Constructor.Inputs); i++ {
			var child *DeployTree
			var err error
			arg := c.ConstructorArgs[i]
			argABI := c.TheABI.Constructor.Inputs[i]

			if argABI.Type.T == abi.AddressTy {
				if addrArg, ok := arg.(common.Address); ok {
					address := strings.ToLower(addrArg.Hex())

					// if _, ok := contractsDone["0xb85a54944b58342b07887942e6f530f616479efd"]; ok {
					// 	fmt.Println("haha: " + address)
					// }

					if cval, ok := c.Manager.ContractsMap[address]; ok {
						if cdone, ok := contractsDone[address]; ok {
							child = cdone
						} else {
							child, err = ContractToDeployTree(cval, contractsDone)
							if err != nil {
								return nil, err
							}
							contractsDone[address] = child
						}
					} else {
						child, err = ContractToDeployTree(arg, contractsDone)
						if err != nil {
							return nil, err
						}
					}
				} else {
					err = fmt.Errorf("The argument ABI is address type but not convertible to common.address")
					return nil, err
				}
			} else {
				child, err = ContractToDeployTree(arg, contractsDone)
				if err != nil {
					return nil, err
				}
			}
			child.Father = node
			node.Children = append(node.Children, child)
		}
	} else {
		switch reflect.TypeOf(v).Kind() {
		case reflect.Slice, reflect.Array:
			var values []interface{}
			s := reflect.ValueOf(v)
			for i := 0; i < s.Len(); i++ {
				value, err := ContractToDeployTree(s.Index(i), contractsDone)
				if err != nil {
					return nil, err
				}
				values = append(values, value)
			}
			node.Value = values
			node.IsContract = false
		default:
			node.Value = v
			node.IsContract = false
		}
	}
	return node, nil
}
