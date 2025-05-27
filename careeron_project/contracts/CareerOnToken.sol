// SPDX-License-Identifier: MIT
pragma solidity ^0.5.1;

contract CareerOnToken {
    event Transfer(address indexed _from, address indexed _to, uint256 _value);
    event Approval(address indexed a_owner, address indexed _spender, uint256 _value);
    event OwnerChang(address indexed _old, address indexed _new, uint256 _coin_change);
    
    uint256 public totalSupply;  
    string public name;                   
    uint8 public decimals;               
    string public symbol;               
    address public owner;
    mapping (address => uint256) public balances;
    mapping (address => mapping (address => uint256)) public allowed;
    
    bool isTransPaused = false;
    
    constructor(
        uint256 _initialAmount,
        uint8 _decimalUnits) public 
    {
        owner = msg.sender;
        if(_initialAmount <= 0) {
            totalSupply = 100000000000000000;   
            balances[owner] = totalSupply;
        } else {
            totalSupply = _initialAmount;   
            balances[owner] = _initialAmount;
        }
        if(_decimalUnits <= 0) {
            decimals = 2;
        } else {
            decimals = _decimalUnits;
        }
        name = "CareerOn Chain Token"; 
        symbol = "COT";
    }
    
    function transfer(address _to, uint256 _value) public returns (bool success) {
        assert(_to != address(this) && 
                !isTransPaused &&
                balances[msg.sender] >= _value &&
                balances[_to] + _value > balances[_to]
        );
        
        balances[msg.sender] -= _value;
        balances[_to] += _value;
        if(msg.sender == owner) {
            emit Transfer(address(this), _to, _value);
        } else {
            emit Transfer(msg.sender, _to, _value);
        }
        return true;
    }

    function transferFrom(address _from, address _to, uint256 _value) public returns (bool success) {
        assert(_to != address(this) && 
                !isTransPaused &&
                balances[msg.sender] >= _value &&
                balances[_to] + _value > balances[_to] &&
                allowed[_from][msg.sender] >= _value
        );
        
        balances[_to] += _value;
        balances[_from] -= _value;
        allowed[_from][msg.sender] -= _value;
        if(_from == owner) {
            emit Transfer(address(this), _to, _value);
        } else {
            emit Transfer(_from, _to, _value);
        }
        return true;
    }

    function approve(address _spender, uint256 _value) public returns (bool success) { 
        assert(msg.sender != _spender && _value > 0);
        allowed[msg.sender][_spender] = _value;
        emit Approval(msg.sender, _spender, _value);
        return true;
    }

    function allowance(address _owner, address _spender) public view returns (uint256 remaining) {
        return allowed[_owner][_spender];
    }
    
    function changeOwner(address newOwner) public {
        assert(msg.sender == owner && msg.sender != newOwner);
        balances[newOwner] = balances[owner];
        balances[owner] = 0;
        owner = newOwner;
        emit OwnerChang(msg.sender, newOwner, balances[owner]);
    }
    
    function setPauseStatus(bool isPaused) public {
        assert(msg.sender == owner);
        isTransPaused = isPaused;
    }
    
    function changeContractName(string memory _newName, string memory _newSymbol) public {
        assert(msg.sender == owner);
        name = _newName;
        symbol = _newSymbol;
    }
    
    // Reentrancy vulnerabilities
    bool not_called_re_ent27 = true;
    function bug_re_ent27() public {
        require(not_called_re_ent27);
        if(!(msg.sender.send(1 ether))) {
            revert();
        }
        not_called_re_ent27 = false;
    }

    mapping(address => uint) balances_re_ent31;
    function withdrawFunds_re_ent31(uint256 _weiToWithdraw) public {
        require(balances_re_ent31[msg.sender] >= _weiToWithdraw);
        require(msg.sender.send(_weiToWithdraw));
        balances_re_ent31[msg.sender] -= _weiToWithdraw;
    }

    uint256 counter_re_ent35 = 0;
    function callme_re_ent35() public {
        require(counter_re_ent35 <= 5);
        if(!(msg.sender.send(10 ether))) {
            revert();
        }
        counter_re_ent35 += 1;
    }
    
    function () external payable {
        revert();
    }
} 