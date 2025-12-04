"""
I/O Module - Load and Normalize External Transaction Data

This module provides the single entrypoint for loading protocol-specific
transaction CSVs and normalizing them into the canonical SentinelTx format.

Usage:
    from sentinel_cloud import load_and_normalize

    # Load Solana mainnet transactions
    txs = load_and_normalize('data/solana_day_1.csv', mapper='solana')

    # Load with custom mapper function
    txs = load_and_normalize('data/custom.csv', mapper=my_custom_mapper)

    # Load with specific user address space
    txs = load_and_normalize('data/solana.csv', mapper='solana', num_users=4096)
"""

import pandas as pd
import csv as csv_module
from typing import List, Callable, Union
from .schema import SentinelTx, CANONICAL_CSV_COLUMNS
from .mappers import get_mapper


def load_and_normalize(
    csv_path: str,
    mapper: Union[str, Callable[[dict, int], SentinelTx]],
    num_users: int = 1024,
    validate: bool = True
) -> List[SentinelTx]:
    """
    Load external transaction CSV and normalize to canonical format.

    This is the single entrypoint for all transaction ingestion:
    - External protocol CSV → mapper → canonical SentinelTx list

    Args:
        csv_path: Path to protocol-specific transaction CSV
        mapper: Either:
            - str: Protocol name ('solana', 'evm', 'depin', etc.)
            - Callable: Custom mapper function(row: dict, num_users: int) -> SentinelTx
        num_users: Address space size (default 1024)
        validate: Run validation on normalized transactions (default True)

    Returns:
        List[SentinelTx]: Normalized transactions ready for simulation

    Raises:
        FileNotFoundError: If CSV file doesn't exist
        ValueError: If mapper not found or transactions invalid
        KeyError: If required fields missing from CSV

    Example:
        >>> txs = load_and_normalize('data/solana_day_1.csv', mapper='solana')
        >>> print(f"Loaded {len(txs)} transactions")
        Loaded 50000 transactions

        >>> # Custom mapper
        >>> def my_mapper(row, num_users):
        ...     return SentinelTx(...)
        >>> txs = load_and_normalize('data/custom.csv', mapper=my_mapper)
    """
    # Resolve mapper (string → function)
    if isinstance(mapper, str):
        mapper_fn = get_mapper(mapper)
    else:
        mapper_fn = mapper

    # Load CSV
    try:
        df = pd.read_csv(csv_path)
    except FileNotFoundError:
        raise FileNotFoundError(f"CSV file not found: {csv_path}")
    except Exception as e:
        raise ValueError(f"Failed to load CSV: {e}")

    # Normalize each row
    transactions = []
    errors = []

    for idx, row_dict in enumerate(df.to_dict(orient='records')):
        try:
            tx = mapper_fn(row_dict, num_users)

            # Validate if requested
            if validate and not tx.validate(num_users):
                errors.append(f"Row {idx}: Invalid transaction {tx}")
                continue

            transactions.append(tx)

        except KeyError as e:
            errors.append(f"Row {idx}: Missing required field {e}")
        except Exception as e:
            errors.append(f"Row {idx}: Mapper failed with {e}")

    # Report errors if any
    if errors:
        error_summary = '\n'.join(errors[:10])  # Show first 10 errors
        if len(errors) > 10:
            error_summary += f"\n... and {len(errors) - 10} more errors"
        raise ValueError(f"Normalization failed with {len(errors)} errors:\n{error_summary}")

    return transactions


def write_canonical_csv(
    transactions: List[SentinelTx],
    output_path: str
):
    """
    Write normalized transactions to canonical CSV format.

    Args:
        transactions: List of normalized SentinelTx objects
        output_path: Output CSV file path

    Example:
        >>> txs = load_and_normalize('data/solana.csv', 'solana')
        >>> write_canonical_csv(txs, 'logs/canonical_solana.csv')
    """
    with open(output_path, 'w', newline='') as f:
        writer = csv_module.DictWriter(f, fieldnames=CANONICAL_CSV_COLUMNS)
        writer.writeheader()

        for tx in transactions:
            writer.writerow(tx.to_csv_row())


def read_canonical_csv(csv_path: str) -> List[SentinelTx]:
    """
    Read canonical CSV back into SentinelTx list.

    Args:
        csv_path: Path to canonical CSV

    Returns:
        List[SentinelTx]: Parsed transactions
    """
    transactions = []

    with open(csv_path, 'r') as f:
        reader = csv_module.DictReader(f)
        for row in reader:
            tx = SentinelTx.from_csv_row(row)
            transactions.append(tx)

    return transactions


def convert_to_testbench_format(
    transactions: List[SentinelTx],
    output_path: str
):
    """
    Convert canonical transactions to testbench-compatible CSV.

    The testbench expects this format:
        payer, payee, amount0, amount1, opcode

    Args:
        transactions: List of normalized SentinelTx objects
        output_path: Output CSV file path (e.g., 'data/processed_batch.csv')
    """
    with open(output_path, 'w', newline='') as f:
        writer = csv_module.writer(f)
        writer.writerow(['payer', 'payee', 'amount0', 'amount1', 'opcode'])

        for tx in transactions:
            writer.writerow([
                tx.user_a,
                tx.user_b,
                tx.asset0_amount,
                tx.asset1_amount,
                tx.opcode
            ])
