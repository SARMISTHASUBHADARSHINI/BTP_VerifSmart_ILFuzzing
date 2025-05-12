#!/bin/bash

set -e  # Exit on any error

# Configurable variables
CONTRACT_NAME="Crowdsale"  # Change this to your contract's name (without .sol)
CONTRACT_FILE="contract.sol"  # Your Solidity file
PORT=8545
PROJECT_DIR="/go/src/ilf/testing/crowdsale"

echo "🔧 Setting up testing environment..."

# Clean existing test directory (optional)
rm -rf "$PROJECT_DIR"
mkdir -p "$PROJECT_DIR/contracts"
cp "$CONTRACT_FILE" "$PROJECT_DIR/contracts/"

# Go to project directory
cd "$PROJECT_DIR"

# Unbox Truffle and install dependencies
echo "📦 Initializing Truffle project..."
echo "📁 Manually creating Truffle project..."
npm init -y > /dev/null
npm install --save-dev truffle@5.0.35
mkdir -p contracts migrations test

# Add a basic Truffle config
cat <<EOF > truffle-config.js
module.exports = {
  networks: {
    development: {
      host: "127.0.0.1",
      port: 8545,
      network_id: "*"
    }
  },
  compilers: {
    solc: {
      version: "0.5.8"
    }
  }
};
EOF

# Add initial migration
cat <<EOF > migrations/1_initial_migration.js
const Migrations = artifacts.require("Migrations");

module.exports = function(deployer) {
  deployer.deploy(Migrations);
};
EOF

# Add Migrations.sol
cat <<EOF > contracts/Migrations.sol
pragma solidity ^0.5.8;

contract Migrations {
  address public owner;
  uint public last_completed_migration;

  constructor() public {
    owner = msg.sender;
  }

  function setCompleted(uint completed) public {
    require(msg.sender == owner);
    last_completed_migration = completed;
  }
}
EOF


# Optional: Customize deployment script
echo "📄 Updating migration script..."
cat <<EOF > migrations/2_deploy_contracts.js
const $CONTRACT_NAME = artifacts.require("$CONTRACT_NAME");

module.exports = function(deployer) {
  deployer.deploy($CONTRACT_NAME);
};
EOF

# Compile contracts
echo "🔨 Compiling contracts..."
truffle compile

# Kill existing ganache if needed
if command -v lsof &> /dev/null && lsof -i :$PORT &> /dev/null; then
  echo "🛑 Killing existing ganache on port $PORT..."
  kill -9 $(lsof -t -i:$PORT)
fi

# Start ganache in background
echo "🚀 Starting ganache-cli on port $PORT..."
ganache-cli -p $PORT > ganache.log 2>&1 &
GANACHE_PID=$!
sleep 3  # Give ganache time to start

cd ../../..  # Go back to ilf root

# Extract transactions
echo "📤 Extracting deployment transactions..."
python3 /go/src/ilf/script/extract.py --proj "$PROJECT_DIR" --port $PORT

# # Run ILF fuzzer - FIX: Use Python module execution instead of direct script invocation
echo "🤖 Running ILF fuzzing..."
cd /go/src/  # Change to the parent directory of the ilf module
PYTHONPATH=/go/src python3 -m ilf.ilf --proj "$PROJECT_DIR" --contract "$CONTRACT_NAME" --fuzzer imitation --model /go/src/ilf/model/ --limit 2000

# Cleanup
echo "🧹 Killing ganache-cli (PID $GANACHE_PID)..."
kill -9 $GANACHE_PID

echo "✅ Fuzzing complete!"
