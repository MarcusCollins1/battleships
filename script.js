
"use strict";

const SETTINGS = {
    easy: {
        size: 6,
        fleet: [3, 2, 1, 1],
        startingClues: 5
    },
    medium: {
        size: 8,
        fleet: [4, 3, 2, 2, 1, 1],
        startingClues: 5
    },
    hard: {
        size: 10,
        fleet: [4, 3, 3, 2, 2, 2, 1, 1, 1, 1],
        startingClues: 2
    }
};

const $ = id => document.getElementById(id);

const boardEl = $("board");
const fleetEl = $("fleet");
const messageEl = $("message");

let game = null;
let timerInterval = null;

function randomInt(max) {
    return Math.floor(Math.random() * max);
}

function shuffle(items) {
    const result = [...items];

    for (let i = result.length - 1; i > 0; i--) {
        const j = randomInt(i + 1);
        [result[i], result[j]] = [result[j], result[i]];
    }

    return result;
}

function emptyGrid(size, value = 0) {
    return Array.from(
        { length: size },
        () => Array(size).fill(value)
    );
}

function cloneGrid(grid) {
    return grid.map(row => [...row]);
}

function getCounts(grid) {
    const size = grid.length;

    return {
        rows: grid.map(row =>
            row.reduce((sum, cell) => sum + cell, 0)
        ),
        cols: Array.from({ length: size }, (_, col) =>
            grid.reduce((sum, row) => sum + row[col], 0)
        )
    };
}

// A ship cannot overlap or touch another ship.
function canPlace(grid, row, col, length, vertical) {
    const size = grid.length;

    for (let i = 0; i < length; i++) {
        const r = row + (vertical ? i : 0);
        const c = col + (vertical ? 0 : i);

        if (r >= size || c >= size) return false;

        for (let dr = -1; dr <= 1; dr++) {
            for (let dc = -1; dc <= 1; dc++) {
                if (grid[r + dr]?.[c + dc] === 1) {
                    return false;
                }
            }
        }
    }

    return true;
}

function placeShip(grid, row, col, length, vertical, value) {
    for (let i = 0; i < length; i++) {
        const r = row + (vertical ? i : 0);
        const c = col + (vertical ? 0 : i);
        grid[r][c] = value;
    }
}

// Generate a random valid hidden fleet.
function generateFleet(size, fleet) {
    const grid = emptyGrid(size);

    function backtrack(index) {
        if (index === fleet.length) return true;

        const length = fleet[index];
        const options = [];

        for (let r = 0; r < size; r++) {
            for (let c = 0; c < size; c++) {
                for (const vertical of [false, true]) {
                    if (length === 1 && vertical) continue;

                    if (canPlace(grid, r, c, length, vertical)) {
                        options.push({ r, c, vertical });
                    }
                }
            }
        }

        for (const option of shuffle(options)) {
            placeShip(
                grid, option.r, option.c,
                length, option.vertical, 1
            );

            if (backtrack(index + 1)) return true;

            placeShip(
                grid, option.r, option.c,
                length, option.vertical, 0
            );
        }

        return false;
    }

    return backtrack(0) ? grid : null;
}

// Build every possible position for a ship.
function makePlacements(size, length) {
    const placements = [];

    for (let r = 0; r < size; r++) {
        for (let c = 0; c < size; c++) {
            for (const vertical of [false, true]) {
                if (length === 1 && vertical) continue;

                const cells = [];
                const neighbors = new Set();

                for (let i = 0; i < length; i++) {
                    const rr = r + (vertical ? i : 0);
                    const cc = c + (vertical ? 0 : i);

                    if (rr >= size || cc >= size) break;

                    cells.push(rr * size + cc);

                    for (let dr = -1; dr <= 1; dr++) {
                        for (let dc = -1; dc <= 1; dc++) {
                            const nr = rr + dr;
                            const nc = cc + dc;

                            if (
                                nr >= 0 && nr < size &&
                                nc >= 0 && nc < size
                            ) {
                                neighbors.add(nr * size + nc);
                            }
                        }
                    }
                }

                if (cells.length !== length) continue;

                const bit = n => 1n << BigInt(n);

                placements.push({
                    cells,
                    mask: cells.reduce(
                        (mask, n) => mask | bit(n), 0n
                    ),
                    blocked: [...neighbors].reduce(
                        (mask, n) => mask | bit(n), 0n
                    ),
                    rows: cells.map(n => Math.floor(n / size)),
                    cols: cells.map(n => n % size)
                });
            }
        }
    }

    return placements;
}

// Count possible solutions, stopping at two.
// A result of 1 means the puzzle is unique.
// A result of 2 means multiple solutions exist.
// null means the search budget was exceeded.
function countSolutions(solution, fleet, givens) {
    const size = solution.length;
    const target = getCounts(solution);
    const lengths = [...fleet].sort((a, b) => b - a);
    const uniqueLengths = [...new Set(lengths)];

    const candidates = Object.fromEntries(
        uniqueLengths.map(length => [
            length,
            makePlacements(size, length).filter(p =>
                p.cells.every(n => {
                    const r = Math.floor(n / size);
                    const c = n % size;
                    return givens[r][c] !== 2;
                })
            )
        ])
    );

    const required = [];
    for (let r = 0; r < size; r++) {
        for (let c = 0; c < size; c++) {
            if (givens[r][c] === 1) {
                required.push(r * size + c);
            }
        }
    }

    const bit = n => 1n << BigInt(n);
    const requiredMask = required.reduce(
        (mask, n) => mask | bit(n), 0n
    );

    const rowUsed = Array(size).fill(0);
    const colUsed = Array(size).fill(0);
    const remaining = Array(lengths.length + 1).fill(0);

    for (let i = lengths.length - 1; i >= 0; i--) {
        remaining[i] = remaining[i + 1] + lengths[i];
    }

    let solutions = 0;
    let nodes = 0;
    const NODE_LIMIT = 80000;

    function search(index, occupied, blocked, lastChoice) {
        if (++nodes > NODE_LIMIT) return false;
        if (solutions >= 2) return true;

        if (index === lengths.length) {
            if (
                rowUsed.some((n, r) => n !== target.rows[r]) ||
                colUsed.some((n, c) => n !== target.cols[c])
            ) return true;

            if ((occupied & requiredMask) !== requiredMask) {
                return true;
            }

            solutions++;
            return true;
        }

        const length = lengths[index];
        const options = candidates[length];
        const sameAsPrevious = index > 0 && lengths[index - 1] === length;
        const start = sameAsPrevious ? lastChoice + 1 : 0;

        for (let i = start; i < options.length; i++) {
            const p = options[i];

            if ((p.mask & blocked) !== 0n) continue;

            let valid = true;

            for (const r of p.rows) rowUsed[r]++;
            for (const c of p.cols) colUsed[c]++;

            for (let j = 0; j < size; j++) {
                if (
                    rowUsed[j] > target.rows[j] ||
                    colUsed[j] > target.cols[j]
                ) {
                    valid = false;
                    break;
                }
            }

            if (valid) {
                const nextOccupied = occupied | p.mask;
                const nextBlocked = blocked | p.blocked;

                // Required ship cells must still be coverable.
                const uncovered = requiredMask & ~nextOccupied;

                if ((uncovered & nextBlocked) === 0n) {
                    valid = search(
                        index + 1,
                        nextOccupied,
                        nextBlocked,
                        i
                    );
                } else {
                    valid = true;
                }
            }

            for (const r of p.rows) rowUsed[r]--;
            for (const c of p.cols) colUsed[c]--;

            if (!valid) return false;
            if (solutions >= 2) return true;
        }

        return true;
    }

  const completed = search(0, 0n, 0n, -1);
  return completed ? Math.min(solutions, 2) : null;
}

// Add clues until there is exactly one solution.
function createPuzzle(level) {
    const config = SETTINGS[level];
    const size = config.size;

    const solution = generateFleet(size, config.fleet);

    if (!solution) {
            throw new Error("Could not generate a fleet.");
    }

    const givens = emptyGrid(size);

    // Limit starting clues so the board is never revealed.
    const clueLimits = {
        easy: 5,
        medium: 4,
        hard: 2
    };

    const positions = shuffle(
        Array.from({ length: size * size }, (_, i) => i)
    );

    const clueCount = clueLimits[level];

    for (let i = 0; i < clueCount; i++) {
        const position = positions[i];
        const r = Math.floor(position / size);
        const c = position % size;

        givens[r][c] = solution[r][c] === 1 ? 1 : 2;
    }

    return {
        level,
        size,
        fleet: [...config.fleet],
        solution,
        givens,
        player: cloneGrid(givens),
        counts: getCounts(solution),
        seconds: 0,
        finished: false,
        clueCount
    };
}

function setMessage(text, type = "") {
    messageEl.textContent = text;
    messageEl.className = "message " + type;
}

function formatTime(seconds) {
    const minutes = Math.floor(seconds / 60);
    const secs = seconds % 60;

    return (
        String(minutes).padStart(2, "0") + ":" +
        String(secs).padStart(2, "0")
    );
}

function startTimer() {
    clearInterval(timerInterval);

    $("timer").textContent = "00:00";

    timerInterval = setInterval(() => {
        if (!game || game.finished) return;

        game.seconds++;
        $("timer").textContent = formatTime(game.seconds);
    }, 1000);
}

function getPlayerShips() {
    const size = game.size;
    const visited = emptyGrid(size, false);
    const ships = [];

    for (let r = 0; r < size; r++) {
        for (let c = 0; c < size; c++) {
            if (game.player[r][c] !== 1 || visited[r][c]) {
                continue;
            }

            const cells = [];
            const stack = [[r, c]];

            while (stack.length) {
                const [row, col] = stack.pop();

                if (
                    row < 0 || row >= size ||
                    col < 0 || col >= size ||
                    visited[row][col] ||
                    game.player[row][col] !== 1
                ) continue;

                visited[row][col] = true;
                cells.push([row, col]);

                stack.push(
                    [row - 1, col],
                    [row + 1, col],
                    [row, col - 1],
                    [row, col + 1]
                );
            }

            const sameRow = cells.every(
                cell => cell[0] === cells[0][0]
            );

            const sameCol = cells.every(
                cell => cell[1] === cells[0][1]
            );

            let valid = sameRow || sameCol;

            // Check for diagonal touching and invalid shapes.
            for (const [row, col] of cells) {
                for (let dr = -1; dr <= 1; dr++) {
                    for (let dc = -1; dc <= 1; dc++) {
                        const nr = row + dr;
                        const nc = col + dc;

                        if (
                            nr < 0 || nr >= size ||
                            nc < 0 || nc >= size
                        ) continue;

                        if (game.player[nr][nc] !== 1) continue;

                        if (
                            !cells.some(([a, b]) => a === nr && b === nc)
                        ) {
                            valid = false;
                        }
                    }
                }
            }

            ships.push({
                length: cells.length,
                cells,
                valid
            });
        }
    }

  return ships;
}

function renderFleet() {
    fleetEl.innerHTML = "";

    const playerShips = getPlayerShips();
    const found = {};

    // Count valid completed ships by length.
    for (const ship of playerShips) {
        if (!ship.valid) continue;

        const length = ship.length;

        if (!game.fleet.includes(length)) continue;

        // A marked ship is complete only if it exactly
        // matches a ship in the generated solution.
        const matchesSolution = ship.cells.every(
            ([r, c]) => game.solution[r][c] === 1
        );

        const solutionCells = ship.cells.flatMap(
            ([r, c]) => {
                return [
                    [r - 1, c],
                    [r + 1, c],
                    [r, c - 1],
                    [r, c + 1]
                ];
            }
        );

        const hasMissingSegment = solutionCells.some(
            ([r, c]) =>
                r >= 0 && r < game.size &&
                c >= 0 && c < game.size &&
                game.solution[r][c] === 1 &&
                game.player[r][c] !== 1
        );

        if (matchesSolution && !hasMissingSegment) {
            found[length] = (found[length] || 0) + 1;
        }
    }

    const used = {};

    for (const length of game.fleet) {
        used[length] = (used[length] || 0) + 1;

        const completed = used[length] <= (found[length] || 0);

        const item = document.createElement("div");
        item.className = "fleet-item";

        if (completed) {
            item.classList.add("found");
        }

        const ship = document.createElement("div");
        ship.className = "fleet-ship";

        for (let i = 0; i < length; i++) {
            const segment = document.createElement("span");
            segment.className = "fleet-segment";
            ship.appendChild(segment);
        }

        const tick = document.createElement("span");
        tick.className = "fleet-tick";
        tick.textContent = completed ? "✓" : "";

        item.appendChild(ship);
        item.appendChild(tick);

        fleetEl.appendChild(item);
    }
}

function renderBoard() {
    const size = game.size;
    boardEl.innerHTML = "";
    boardEl.style.setProperty("--size", size);

    const playerCounts = getCounts(
        game.player.map(row =>
            row.map(cell => cell === 1 ? 1 : 0)
        )
    );

    // Column clues at the top
    for (let c = 0; c < size; c++) {
        const clue = document.createElement("div");
        clue.className = "clue";

        const target = game.counts.cols[c];
        const current = playerCounts.cols[c];

        clue.textContent = target;

        if (current === target) clue.classList.add("complete");
        if (current > target) clue.classList.add("over");

        boardEl.appendChild(clue);
    }

    boardEl.appendChild(document.createElement("div"));

    // Cells and row clues
    for (let r = 0; r < size; r++) {
        for (let c = 0; c < size; c++) {
            const cell = document.createElement("button");
            const state = game.player[r][c];
            const given = game.givens[r][c] !== 0;

            cell.type = "button";
            cell.className = "cell";

            if (state === 1) {
                cell.classList.add("ship");

                // Check adjacent ship segments
                const up = r > 0 && game.player[r - 1][c] === 1;
                const down = r < size - 1 && game.player[r + 1][c] === 1;
                const left = c > 0 && game.player[r][c - 1] === 1;
                const right = c < size - 1 && game.player[r][c + 1] === 1;

                // Determine ship orientation and shape
                if (left || right) {
                    cell.classList.add("horizontal");

                    if (!left) cell.classList.add("start");
                    if (!right) cell.classList.add("end");

                } else if (up || down) {
                    cell.classList.add("vertical");

                    if (!up) cell.classList.add("start");
                    if (!down) cell.classList.add("end");

                } else {
                    cell.classList.add("single");
                }

            } else if (state === 2) {
                cell.classList.add("water");
                cell.textContent = "";
            }

            if (given) cell.classList.add("given");

            cell.disabled = given || game.finished;
            cell.setAttribute(
                "aria-label",
                `Row ${r + 1}, column ${c + 1}, ` +
                (state === 1 ? "ship" :
                state === 2 ? "water" : "unknown")
            );

            cell.addEventListener("click", () => {
                if (game.finished || given) return;

                game.player[r][c] = (game.player[r][c] + 1) % 3;

                renderBoard();
                setMessage("");
            });

            boardEl.appendChild(cell);
        }

        const clue = document.createElement("div");
        clue.className = "clue";

        const target = game.counts.rows[r];
        const current = playerCounts.rows[r];

        clue.textContent = target;

        if (current === target) clue.classList.add("complete");
        if (current > target) clue.classList.add("over");

        boardEl.appendChild(clue);
    }
    renderFleet();
}

function checkAnswer() {
    if (!game || game.finished) return;

    const ships = getPlayerShips();

    if (ships.some(ship => !ship.valid)) {
        setMessage(
            "Some ships are bent or touching other ships.",
            "error"
        );
        return;
    }

    const actualFleet = ships
        .map(ship => ship.length)
        .sort((a, b) => b - a);

  const expectedFleet = [...game.fleet]
    .sort((a, b) => b - a);

  if (
    JSON.stringify(actualFleet) !==
    JSON.stringify(expectedFleet)
    ) {
        setMessage(
            "The fleet is not complete yet.",
            "error"
        );
        return;
    }

    const counts = getCounts(
        game.player.map(row =>
            row.map(cell => cell === 1 ? 1 : 0)
        )
    );

    const rowsCorrect = counts.rows.every(
        (n, i) => n === game.counts.rows[i]
    );

    const colsCorrect = counts.cols.every(
        (n, i) => n === game.counts.cols[i]
    );

    if (!rowsCorrect || !colsCorrect) {
        setMessage(
            "Some row or column totals are incorrect.",
            "error"
        );
        return;
    }

    // Starting clues must still be respected.
    for (let r = 0; r < game.size; r++) {
        for (let c = 0; c < game.size; c++) {
            if (
                game.givens[r][c] === 2 &&
                game.player[r][c] === 1
            ) {
                setMessage(
                    "A water clue has been marked as a ship.",
                    "error"
                );
                return;
            }

            if (
                game.givens[r][c] === 1 &&
                game.player[r][c] !== 1
            ) {
                setMessage(
                    "A ship clue is missing.",
                    "error"
                );
                return;
            }
        }
    }

    game.finished = true;
    clearInterval(timerInterval);
    renderBoard();

    setMessage(
        `Congratulations! Solved in ${formatTime(game.seconds)}!`,
        "success"
    );
}

function giveHint() {
    if (!game || game.finished) return;

    const options = [];

    for (let r = 0; r < game.size; r++) {
        for (let c = 0; c < game.size; c++) {
            if (game.givens[r][c] !== 0) continue;

            const correct = game.solution[r][c] === 1 ? 1 : 2;

            if (game.player[r][c] !== correct) {
                options.push({ r, c, correct });
            }
        }
    }

    if (!options.length) {
        checkAnswer();
        return;
    }

    const hint = options[randomInt(options.length)];

    game.player[hint.r][hint.c] = hint.correct;
    game.givens[hint.r][hint.c] = hint.correct;

    renderBoard();
    setMessage("A correct square has been revealed.");
}

function clearBoard() {
    if (!game || game.finished) return;

    game.player = cloneGrid(game.givens);
    renderBoard();
    setMessage("Board cleared.");
}

function revealSolution() {
    if (!game || game.finished) return;

    const confirmed = confirm("Reveal the solution? This will end the puzzle.");

    if (!confirmed) return;

    game.player = game.solution.map(row =>
        row.map(cell => cell === 1 ? 1 : 2)
    );

    game.finished = true;
    clearInterval(timerInterval);
    renderBoard();

    setMessage("Solution revealed.");
}

function newGame() {
    const level = $("difficulty").value;

    clearInterval(timerInterval);
    setMessage("Generating puzzle...");

    // Allow the status message to render first.
    setTimeout(() => {
            try {
                game = createPuzzle(level);

                $("difficultyLabel").textContent = level.charAt(0).toUpperCase() + level.slice(1);

                renderFleet();
                renderBoard();
                startTimer();

                setMessage(`New puzzle ready! ${game.clueCount} starting clues.`);
            } catch (error) {
                console.error(error);
                setMessage(
                    "Generation failed. Please try New Puzzle.",
                    "error"
                );
            }
    }, 20);
}

$("returnBtn").addEventListener("click", () => {
    window.location.href = "../";
});
$("newGameBtn").addEventListener("click", newGame);
$("checkBtn").addEventListener("click", checkAnswer);
$("hintBtn").addEventListener("click", giveHint);
$("clearBtn").addEventListener("click", clearBoard);
$("revealBtn").addEventListener("click", revealSolution);

newGame();
