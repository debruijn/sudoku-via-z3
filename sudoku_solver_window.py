from tkinter import Tk, Canvas, Frame, Button, BOTH, TOP, BOTTOM

import sudoku_solver
from functools import partial

BOARDS = ['debug', 'n00b', 'l33t', 'error']  # Available sudoku boards - will be dropped in future
BOARDS_ALT = ['classic', 'diagonal']  # Extra sudoku boards with an alternative naming scheme
MARGIN = 50  # Pixels around the board
SIDE = 100  # Width of every board cell.
WIDTH = HEIGHT = MARGIN * 2 + SIDE * 9  # Width and height of the whole board

CURR_ROW, CURR_COL = -1, -1


def draw_grid(grid_canvas):
    """
    Draws grid divided with blue lines into 3x3 squares
    """
    for i in range(10):
        color = "blue" if i % 3 == 0 else "gray"

        x0 = MARGIN + i * SIDE
        y0 = MARGIN
        x1 = MARGIN + i * SIDE
        y1 = HEIGHT - MARGIN
        grid_canvas.create_line(x0, y0, x1, y1, fill=color)

        x0 = MARGIN
        y0 = MARGIN + i * SIDE
        x1 = WIDTH - MARGIN
        y1 = MARGIN + i * SIDE
        grid_canvas.create_line(x0, y0, x1, y1, fill=color)


def draw_puzzle(grid_canvas, input):
    grid_canvas.delete("numbers")
    color = "black"  # to add: make color dependent on if its given or not

    for key, value in input.items():
        x = MARGIN + key[1] * SIDE + SIDE / 2
        y = MARGIN + key[0] * SIDE + SIDE / 2
        grid_canvas.create_text(x, y, text=value, tags='numbers', font=('Arial', 25), fill=color)


def draw_cursor(grid_canvas, row, col):
    grid_canvas.delete("cursor")
    if row >= 0 and col >= 0:
        x0 = MARGIN + col * SIDE + 1
        y0 = MARGIN + row * SIDE + 1
        x1 = MARGIN + (col + 1) * SIDE - 1
        y1 = MARGIN + (row + 1) * SIDE - 1
        grid_canvas.create_rectangle(
            x0, y0, x1, y1,
            outline="red", tags="cursor"
        )


def cell_clicked(grid_canvas, event):
    x, y = event.x, event.y
    if MARGIN < x < WIDTH - MARGIN and MARGIN < y < HEIGHT - MARGIN:
        grid_canvas.focus_set()

        # get row and col numbers from x,y coordinates
        new_row, new_col = int((y - MARGIN) / SIDE), int((x - MARGIN) / SIDE)

        # if cell was selected already - deselect it
        if (CURR_ROW, CURR_COL) == (new_row, new_col):
            row, col = -1, -1
        else:  # to add: check if number not given, then it should not be overridable
            row, col = new_row, new_col
    else:
        row, col = -1, -1

    draw_cursor(grid_canvas, row, col)


if __name__ == '__main__':

    board_name = "classic"
    filename = f"{board_name}.sudoku" if board_name in BOARDS else f"sudoku_{board_name}"

    with open(filename, 'r') as boards_file2:
        input, extra = sudoku_solver.read_sudoku(boards_file2)
        solve = sudoku_solver.solve_sudoku(input, ['classic'], extra_input=extra)

        root = Tk()
        root.title('Sudoku')
        frame = Frame(root)
        frame.pack(fill=BOTH)
        canvas = Canvas(frame, width=WIDTH, height=HEIGHT)
        canvas.pack(fill=BOTH, side=TOP)

        reset_button = Button(frame, text="Reset puzzle", command=partial(print, 'Hi'))  # command = clear_answers()
        reset_button.pack(fill=BOTH, side=BOTTOM)

        solve_button = Button(frame, text="Solve puzzle", command=partial(print, 'Hi'))  # command = solve
        solve_button.pack(fill=BOTH, side=BOTTOM)

        draw_grid(canvas)
        draw_puzzle(canvas, input)

        # canvas.bind("<Button-1>", partial(print, 'Hi'))
        canvas.bind("<Button-1>", lambda event: canvas.focus_set())
        # canvas.bind("<Key>", partial(print, 'Key'))
        canvas.bind("<Key>", lambda x: print('Key ' + x.char))


        # SudokuUI(root, game)
        root.geometry(f"{WIDTH}x{HEIGHT+65}")
        root.mainloop()
