import numpy as np
from z3 import sat

from witness import find_witnesses


def get_matrix_input():
  print('--- Matrix A Input (Ax >= b) ---')
  print(
      'Note: Each row must have 4 elements (corresponding to 4 variables in'
      ' space).'
  )
  rows = int(input('Enter number of rows in matrix A: '))

  A = []
  for i in range(rows):
    while True:
      try:
        row_input = input()
        row = [float(x) for x in row_input.strip().split()]
        if len(row) != 4:
          print('Error: Each row must contain exactly 4 numbers. Try again.')
          continue
        A.append(row)
        break
      except ValueError:
        print('Invalid input. Please enter numbers only.')
  return A


def get_vector_input(nrows):
  print('\n--- Vector b Input (Ax >= b) ---')
  b = []
  for i in range(nrows):
    while True:
      try:
        val = float(input())
        b.append(val)
        break
      except ValueError:
        print('Invalid input. Please enter a valid number.')
  return b


def main():
  print('=== Z3 Witness Finder Supplementary Program ===\n')

  # 1. Get user input for A and b
  A = get_matrix_input()
  b = get_vector_input(len(A))

  print('\nRunning find_witnesses... Please wait.')

  # 2. Process with your functions
  results = find_witnesses(A, b)

  # 3. Format and output the findings
  print('\n========================================')
  print('          FINDINGS & WITNESSES          ')
  print('========================================')

  print(f"Set is not empty: {results.get('not_empty')}")
  print(f"Set is bounded:   {results.get('bounded')}")

  # Print status or formatted model for each witness type
  witness_types = ['point', 'ray', 'line', 'cone', 'half_plane']

  for w_type in witness_types:
    if w_type in results:
      val = results[w_type]
      print(f'\n--- Witness type: {w_type.upper()} ---')
      if val == sat:
        print('SAT (Model found, but formatting was not applied)')
      elif isinstance(val, str):
        # This will contain your nicely formatted string from format_model
        print(val)
      else:
        print(str(val))

  print('\n========================================')


if __name__ == '__main__':
  main()