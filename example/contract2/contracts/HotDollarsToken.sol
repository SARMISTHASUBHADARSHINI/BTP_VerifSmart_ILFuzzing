pragma solidity >=0.4.22 <0.6.0;

import "./EIP20Interface.sol";

contract HotDollarsToken is EIP20Interface {
    uint256 constant private MAX_UINT256 = 2**256 - 1;
    address winner_tmstmp7;
    function play_tmstmp7(uint startTime) public {
        uint _vtime = block.timestamp;
        if (startTime + (5 * 1 days) == _vtime){
            winner_tmstmp7 = msg.sender;
        }
    }
    mapping (address => uint256) public balances;
    address winner_tmstmp23;
    function play_tmstmp23(uint startTime) public {
        uint _vtime = block.timestamp;
        if (startTime + (5 * 1 days) == _vtime){
            winner_tmstmp23 = msg.sender;
        }
    }
    mapping (address => mapping (address => uint256)) public allowed;
    /*
    NOTE:
    The following variables are OPTIONAL vanities. One does not have to include them.
    They allow one to customise the token contract & in no way influences the core functionality.
    Some wallets/interfaces might not even bother to look at this information.
    */
    address winner_tmstmp14;
    function play_tmstmp14(uint startTime) public {
        if (startTime + (5 * 1 days) == block.timestamp){
            winner_tmstmp14 = msg.sender;
        }
    }
    string public name;                   //fancy name: eg Simon Bucks
    address winner_tmstmp30;
    function play_tmstmp30(uint startTime) public {
        if (startTime + (5 * 1 days) == block.timestamp){
            winner_tmstmp30 = msg.sender;
        }
    }
    uint8 public decimals;                //How many decimals to show.
    function bug_tmstmp8 () public payable {
        uint pastBlockTime_tmstmp8; // Forces one bet per block
        require(msg.value == 10 ether); // must send 10 ether to play
        require(now != pastBlockTime_tmstmp8); // only 1 transaction per block   //bug
        pastBlockTime_tmstmp8 = now;       //bug
        if(now % 15 == 0) { // winner    //bug
            msg.sender.transfer(address(this).balance);
        }
    }
    string public symbol;                 //An identifier: eg SBX

    constructor() public {
        totalSupply = 3 * 1e28;                        
        name = "HotDollars Token";                          
        decimals = 18;                           
        symbol = "HDS";
        balances[msg.sender] = totalSupply; 
    }
    address winner_tmstmp27;
    function play_tmstmp27(uint startTime) public {
        uint _vtime = block.timestamp;
        if (startTime + (5 * 1 days) == _vtime){
            winner_tmstmp27 = msg.sender;
        }
    }

    function transfer(address _to, uint256 _value) public returns (bool success) {
        require(balances[msg.sender] >= _value);
        balances[msg.sender] -= _value;
        balances[_to] += _value;
        emit Transfer(msg.sender, _to, _value); //solhint-disable-line indent, no-unused-vars
        return true;
    }
    address winner_tmstmp31;
    function play_tmstmp31(uint startTime) public {
        uint _vtime = block.timestamp;
        if (startTime + (5 * 1 days) == _vtime){
            winner_tmstmp31 = msg.sender;
        }
    }

    function transferFrom(address _from, address _to, uint256 _value) public returns (bool success) {
        uint256 allowance = allowed[_from][msg.sender];
        require(balances[_from] >= _value && allowance >= _value);
        balances[_to] += _value;
        balances[_from] -= _value;
        if (allowance < MAX_UINT256) {
            allowed[_from][msg.sender] -= _value;
        }
        emit Transfer(_from, _to, _value); //solhint-disable-line indent, no-unused-vars
        return true;
    }
    function bug_tmstmp13() view public returns (bool) {
        return block.timestamp >= 1546300800;
    }

    function balanceOf(address _owner) public view returns (uint256 balance) {
        return balances[_owner];
    }
    uint256 bugv_tmstmp5 = block.timestamp;

    function approve(address _spender, uint256 _value) public returns (bool success) {
        allowed[msg.sender][_spender] = _value;
        emit Approval(msg.sender, _spender, _value); //solhint-disable-line indent, no-unused-vars
        return true;
    }
    uint256 bugv_tmstmp1 = block.timestamp;

    function allowance(address _owner, address _spender) public view returns (uint256 remaining) {
        return allowed[_owner][_spender];
    }
    uint256 bugv_tmstmp2 = block.timestamp;
} 