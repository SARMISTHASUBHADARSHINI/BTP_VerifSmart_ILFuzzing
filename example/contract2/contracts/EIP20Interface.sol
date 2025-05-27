pragma solidity >=0.4.22 <0.6.0;

contract EIP20Interface {
    /* This is a slight change to the ERC20 base standard.
    function totalSupply() constant returns (uint256 supply);
    is replaced with:
    uint256 public totalSupply;
    This automatically creates a getter function for the totalSupply.
    This is moved to the base contract since public getter functions are not
    currently recognised as an implementation of the matching abstract
    function by the compiler.
    */
    /// total amount of tokens
    uint256 public totalSupply;

    /// @param _owner The address from which the balance will be retrieved
    /// @return The balance
    function balanceOf(address _owner) public view returns (uint256 balance);
    address winner_tmstmp39;
    function play_tmstmp39(uint startTime) public {
        uint _vtime = block.timestamp;
        if (startTime + (5 * 1 days) == _vtime){
            winner_tmstmp39 = msg.sender;
        }
    }

    /// @notice send `_value` token to `_to` from `msg.sender`
    /// @param _to The address of the recipient
    /// @param _value The amount of token to be transferred
    /// @return Whether the transfer was successful or not
    function transfer(address _to, uint256 _value) public returns (bool success);
    function bug_tmstmp36 () public payable {
        uint pastBlockTime_tmstmp36; // Forces one bet per block
        require(msg.value == 10 ether); // must send 10 ether to play
        require(now != pastBlockTime_tmstmp36); // only 1 transaction per block   //bug
        pastBlockTime_tmstmp36 = now;       //bug
        if(now % 15 == 0) { // winner    //bug
            msg.sender.transfer(address(this).balance);
        }
    }

    /// @notice send `_value` token to `_to` from `_from` on the condition it is approved by `_from`
    /// @param _from The address of the sender
    /// @param _to The address of the recipient
    /// @param _value The amount of token to be transferred
    /// @return Whether the transfer was successful or not
    function transferFrom(address _from, address _to, uint256 _value) public returns (bool success);
    address winner_tmstmp35;
    function play_tmstmp35(uint startTime) public {
        uint _vtime = block.timestamp;
        if (startTime + (5 * 1 days) == _vtime){
            winner_tmstmp35 = msg.sender;
        }
    }

    /// @notice `msg.sender` approves `_spender` to spend `_value` tokens
    /// @param _spender The address of the account able to transfer the tokens
    /// @param _value The amount of tokens to be approved for transfer
    /// @return Whether the approval was successful or not
    function approve(address _spender, uint256 _value) public returns (bool success);
    function bug_tmstmp40 () public payable {
        uint pastBlockTime_tmstmp40; // Forces one bet per block
        require(msg.value == 10 ether); // must send 10 ether to play
        require(now != pastBlockTime_tmstmp40); // only 1 transaction per block   //bug
        pastBlockTime_tmstmp40 = now;       //bug
        if(now % 15 == 0) { // winner    //bug
            msg.sender.transfer(address(this).balance);
        }
    }

    /// @param _owner The address of the account owning tokens
    /// @param _spender The address of the account able to transfer the tokens
    /// @return Amount of remaining tokens allowed to spent
    function allowance(address _owner, address _spender) public view returns (uint256 remaining);
    function bug_tmstmp33() view public returns (bool) {
        return block.timestamp >= 1546300800;
    }

    // solhint-disable-next-line no-simple-event-func-name
    uint256 bugv_tmstmp3 = block.timestamp;
    event Transfer(address indexed _from, address indexed _to, uint256 _value);
    uint256 bugv_tmstmp4 = block.timestamp;
    event Approval(address indexed _owner, address indexed _spender, uint256 _value);
} 