package data_collect

import (
	"fmt"
	"math/big"
	"reflect"
	"strconv"
	"strings"

	"github.com/ethereum/go-ethereum/accounts/abi"
)

type DeployTree struct {
	Value      interface{}
	VarType    string
	VarName    string
	IsContract bool
	Children   []*DeployTree
	Father     *DeployTree
}

type Deploy struct {
	Tree               *DeployTree
	PostOrderContracts []*DeployTree
}

func (node *DeployTree) ToContract(manager *ContractManager) (*VerifiedContract, error) {
	if address, ok := node.Value.(string); ok {
		if c, ok := manager.ContractsMap[address]; ok {
			return c, nil
		}
		err := fmt.Errorf("cannot find address %s in contract manager", address)
		return nil, err
	}

	err := fmt.Errorf("cannot cast to string type")
	return nil, err
}

func (tree *DeployTree) PostOrderTraversal(addedNode map[string]bool, manager *ContractManager) ([]*DeployTree, error) {
	var nodes []*DeployTree

	// this is for cyclic contracts
	// if tree.IsContract {
	// 	c, err := tree.ToContract(manager)
	// 	if err != nil {
	// 		return nil, err
	// 	}

	// 	addedNode[c.Address] = true
	// }

	for _, child := range tree.Children {
		var newNodes []*DeployTree
		var err error

		if child.IsContract {
			if _, ok := addedNode[child.Value.(string)]; !ok {
				newNodes, err = child.PostOrderTraversal(addedNode, manager)
				if err != nil {
					return nil, err
				}
			}
		} else {
			newNodes, err = child.PostOrderTraversal(addedNode, manager)
			if err != nil {
				return nil, err
			}
		}

		for _, node := range newNodes {
			if node.IsContract {
				nodes = append(nodes, node)
			}
		}
	}

	if tree.IsContract {
		c, err := tree.ToContract(manager)
		if err != nil {
			return nil, err
		}

		if _, ok := addedNode[c.Address]; !ok {
			nodes = append(nodes, tree)
			addedNode[c.Address] = true
		}
	} else {
		kind := reflect.TypeOf(tree.Value).Kind()
		if kind == reflect.Slice || kind == reflect.Array {
			s := reflect.ValueOf(tree.Value)
			for i := 0; i < s.Len(); i++ {
				if t, ok := s.Index(i).Interface().(*DeployTree); ok {
					newNodes, err := t.PostOrderTraversal(addedNode, manager)
					if err != nil {
						return nil, err
					}
					for _, node := range newNodes {
						if node.IsContract {
							nodes = append(nodes, node)
						}
					}
				}
			}
		}
	}

	return nodes, nil
}

func (deploy *Deploy) AssignVarToContract(mCount map[string]int, mainContract *VerifiedContract, manager *ContractManager) error {
	for _, node := range deploy.PostOrderContracts {
		c, err := node.ToContract(manager)
		if err != nil {
			return err
		}

		// node.VarType = fmt.Sprintf("%s_%s", c.Name, mainContract.Address)
		// if count, ok := mCount[c.Name]; ok {
		// 	node.VarName = fmt.Sprintf("%s_%d_%s", c.Name, count, mainContract.Address)
		// 	mCount[c.Name] = count + 1
		// } else {
		// 	count = 0
		// 	node.VarName = fmt.Sprintf("%s_%d_%s", c.Name, count, mainContract.Address)
		// 	mCount[c.Name] = count + 1
		// }

		node.VarType = fmt.Sprintf("%s_%s", c.Name, c.Address)
		if count, ok := mCount[node.VarType]; ok {
			node.VarName = fmt.Sprintf("%s_%d_%s", c.Name, count, c.Address)
			mCount[c.Name] = count + 1
		} else {
			count = 0
			node.VarName = fmt.Sprintf("%s_%d_%s", c.Name, count, c.Address)
			mCount[node.VarType] = count + 1
		}
	}

	return nil
}

func (tree *DeployTree) ValueToString(typ abi.Type) (string, error) {
	if tree.IsContract {
		return fmt.Sprintf("%s.address", tree.VarName), nil
	}

	value := tree.Value

	var stringValue string

	switch typ.T {
	case abi.SliceTy, abi.ArrayTy:
		if typ.Elem != nil {
			var stringValues []string
			s := reflect.ValueOf(value)
			for i := 0; i < s.Len(); i++ {
				if t, ok := s.Index(i).Interface().(*DeployTree); ok {
					stringV, err := t.ValueToString(*typ.Elem)
					if err != nil {
						return "", err
					}
					stringValues = append(stringValues, stringV)
				} else {
					err := fmt.Errorf("elements of slice of array cannot be casted to *DeployTree")
					return "", err
				}
			}
			if len(stringValues) > 0 {
				stringValue = "[" + strings.Join(stringValues, ",") + "]"
			} else {
				stringValue = "[]"
			}
		} else {
			err := fmt.Errorf("field Elem of Type is nil")
			return "", err
		}
	case abi.StringTy:
		stringValue = fmt.Sprintf("\"%s\"", value)
	case abi.IntTy, abi.UintTy:
		switch value.(type) {
		case uint8, int8, uint16, int16, uint32, int32, uint64, int64:
			stringValue = fmt.Sprintf("%v", value)
		case *big.Int:
			stringValue = fmt.Sprintf("web3.toBigNumber(\"0x%x\")", value)
		}
	case abi.BoolTy:
		stringValue = "false"
		if value == true {
			stringValue = "true"
		}
	case abi.AddressTy:
		stringValue = "web3.eth.accounts[0]"
	case abi.BytesTy, abi.FixedBytesTy:
		var stringValues []string
		s := reflect.ValueOf(value)
		for i := 0; i < s.Len(); i++ {
			if b, ok := s.Index(i).Interface().(*DeployTree); ok {
				stringValues = append(stringValues, strconv.FormatInt(int64(b.Value.(reflect.Value).Interface().(byte)), 10))
			} else {
				err := fmt.Errorf("the value of the children of bytes type is not *DeployTree")
				return "", err
			}
		}
		if len(stringValues) > 0 {
			stringValue = "[" + strings.Join(stringValues, ",") + "]"
		} else {
			stringValue = "[]"
		}
	default:
		err := fmt.Errorf("unsupported constructor argument type %v %v", value, reflect.TypeOf(value))
		return "", err
	}

	return stringValue, nil
}

func (tree *DeployTree) ContractToJSArgs(manager *ContractManager) (string, error) {
	if !tree.IsContract {
		err := fmt.Errorf("call ContractToJSArgs with non-contract node as the receiver")
		return "", err
	}

	contract, err := tree.ToContract(manager)
	if err != nil {
		return "", err
	}
	if len(contract.TheABI.Constructor.Inputs) != len(tree.Children) {
		err := fmt.Errorf("The length of contructor ABI is not equal to number of arguments")
		return "", err
	}

	var args []string
	args = append(args, tree.VarName)

	for i := 0; i < len(tree.Children); i++ {
		child := tree.Children[i]
		arg := contract.TheABI.Constructor.Inputs[i]
		stringValue, err := child.ValueToString(arg.Type)
		if err != nil {
			return "", err
		}
		args = append(args, stringValue)
	}

	argsString := strings.Join(args, ", ")

	// return "deployer.deploy(" + argsString + ", {gas: 100000000})", nil
	return "deployer.deploy(" + argsString + ")", nil
}

func (deploy *Deploy) ToJSVarCode() string {
	var defs []string

	for _, v := range deploy.PostOrderContracts {
		def := fmt.Sprintf("var %s = artifacts.require(\"%s\");", v.VarName, v.VarType)
		defs = append(defs, def)
	}

	return strings.Join(defs, "\n")
}

func (deploy *Deploy) ToJSDeployCode(manager *ContractManager) (string, error) {
	code := "  deployer.then(async () => {\n"
	code += "    try {\n"

	// for i, node := range deploy.PostOrderContracts {
	for _, node := range deploy.PostOrderContracts {
		codeCurrentNode, err := node.ContractToJSArgs(manager)
		if err != nil {
			return "", err
		}

		code += "      await " + codeCurrentNode + ";\n"
	}

	code += "    } catch (e) {}\n"
	code += "  });"

	code = "module.exports = function (deployer) {\n" + code + "\n};"

	return code, nil
}
