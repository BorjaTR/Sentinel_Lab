"""
Sentinel Cloud - Chain-Agnostic Transaction Normalization

Public API for loading and normalizing external transaction data
into the canonical SentinelTx format for hardware simulation.

Usage:
    from sentinel_cloud import load_and_normalize, convert_to_testbench_format

    # Load Solana transactions
    txs = load_and_normalize('data/solana_day_1.csv', mapper='solana')

    # Convert to testbench format
    convert_to_testbench_format(txs, 'data/processed_batch.csv')
"""

from .io import load_and_normalize, write_canonical_csv, read_canonical_csv, convert_to_testbench_format
from .schema import SentinelTx, Opcode, CANONICAL_CSV_COLUMNS, VALID_ROLES, validate_role
from .mappers import (
    normalize_solana,
    normalize_evm_erc20,
    normalize_depin_rewards,
    normalize_depin_penalty,
    get_mapper,
    hash_address_to_user_id
)
from .experiment import (
    Config,
    RunResult,
    ExperimentResult,
    run_scenario,
    run_experiments,
    generate_fee_sweep_configs
)

__all__ = [
    # I/O functions
    'load_and_normalize',
    'write_canonical_csv',
    'read_canonical_csv',
    'convert_to_testbench_format',

    # Schema
    'SentinelTx',
    'Opcode',
    'CANONICAL_CSV_COLUMNS',
    'VALID_ROLES',
    'validate_role',

    # Mappers
    'normalize_solana',
    'normalize_evm_erc20',
    'normalize_depin_rewards',
    'normalize_depin_penalty',
    'get_mapper',
    'hash_address_to_user_id',

    # Experiment Engine
    'Config',
    'RunResult',
    'ExperimentResult',
    'run_scenario',
    'run_experiments',
    'generate_fee_sweep_configs',
]

__version__ = '0.2.0'
