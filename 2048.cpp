#include <ctype.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <algorithm>

#include "2049.h"


#include "config.h"
#if defined(HAVE_UNORDERED_MAP)
    #include <unordered_map>
    typedef std::unordered_map<board_t, float> trans_table_t;
#elif defined(HAVE_TR1_UNORDERED_MAP)
    #include <tr1/unordered_map>
    typedef std::tr1::unordered_map<board_t, float> trans_table_t;
#else
    #include <map>
    typedef std::map<board_t, float> trans_table_t;
#endif

/* MSVC compatibility: undefine max and min macros */
#if defined(max)
#undef max
#endif

#if defined(min)
#undef min
#endif

// Transpose rows/columns in a board:
//   0123       048c
//   4567  -->  159d
//   89ab       26ae
//   cdef       37bf
static inline board_t transpose(board_t x)
{
	board_t a1 = x & 0xF0F00F0FF0F00F0FULL;
	board_t a2 = x & 0x0000F0F00000F0F0ULL;
	board_t a3 = x & 0x0F0F00000F0F0000ULL;
	board_t a = a1 | (a2 << 12) | (a3 >> 12);
	board_t b1 = a & 0xFF00FF0000FF00FFULL;
	board_t b2 = a & 0x00FF00FF00000000ULL;
	board_t b3 = a & 0x00000000FF00FF00ULL;
	return b1 | (b2 >> 24) | (b3 << 24);
}

// Count the number of empty positions (= zero nibbles) in a board.
// Precondition: the board cannot be fully empty.
static int count_empty(uint64_t x)
{
	x |= (x >> 2) & 0x3333333333333333ULL;
	x |= (x >> 1);
	x = ~x & 0x1111111111111111ULL;
	// At this point each nibble is:
	//  0 if the original nibble was non-zero
	//  1 if the original nibble was zero
	// Next sum them all
	x += x >> 32;
	x += x >> 16;
	x += x >>  8;
	x += x >>  4; // this can overflow to the next nibble if there were 16 empty positions
	return x & 0xf;
}

/* We can perform state lookups one row at a time by using arrays with 65536 entries. */

/* Move tables. Each row or compressed column is mapped to (oldrow^newrow) assuming row/col 0.
 *
 * Thus, the value is 0 if there is no move, and otherwise equals a value that can easily be
 * xor'ed into the current board state to update the board. */
static row_t row_left_table [65536];
static row_t row_right_table[65536];
static board_t col_up_table[65536];
static board_t col_down_table[65536];
static float heur_score_table[65536];
static float score_table[65536];

void init_tables() {
    for (unsigned row = 0; row < 65536; ++row) {
        unsigned line[4] = {
                (row >>  0) & 0xf,
                (row >>  4) & 0xf,
                (row >>  8) & 0xf,
                (row >> 12) & 0xf
        };

        float heur_score = 0.0f;
        float score = 0.0f;
        for (int i = 0; i < 4; ++i) {
            int rank = line[i];
            if (rank == 0) {
                heur_score += 10000.0f;
            } else if (rank >= 2) {
                // the score is the total sum of the tile and all intermediate merged tiles
                score += (rank - 1) * (1 << rank);
            }
        }
        score_table[row] = score;

        int maxi = 0;
        for (int i = 1; i < 4; ++i) {
            if (line[i] > line[maxi]) maxi = i;
        }

        if (maxi == 0 || maxi == 3) heur_score += 20000.0f;

        // Check if maxi's are close to each other, and of diff ranks (eg 128 256)
        for (int i = 1; i < 4; ++i) {
            if ((line[i] == line[i - 1] + 1) || (line[i] == line[i - 1] - 1)) heur_score += 1000.0f;
        }

        // Check if the values are ordered:
        if ((line[0] < line[1]) && (line[1] < line[2]) && (line[2] < line[3])) heur_score += 10000.0f;
        if ((line[0] > line[1]) && (line[1] > line[2]) && (line[2] > line[3])) heur_score += 10000.0f;

        heur_score_table[row] = heur_score;


        // execute a move to the left
        for (int i = 0; i < 3; ++i) {
            int j;
            for (j = i + 1; j < 4; ++j) {
                if (line[j] != 0) break;
            }
            if (j == 4) break; // no more tiles to the right

            if (line[i] == 0) {
                line[i] = line[j];
                line[j] = 0;
                i--; // retry this entry
            } else if (line[i] == line[j] && line[i] != 0xf) {
                line[i]++;
                line[j] = 0;
            }
        }

        row_t result = (line[0] <<  0) |
                       (line[1] <<  4) |
                       (line[2] <<  8) |
                       (line[3] << 12);
        row_t rev_result = reverse_row(result);
        unsigned rev_row = reverse_row(row);

        row_left_table [    row] =                row  ^                result;
        row_right_table[rev_row] =            rev_row  ^            rev_result;
        col_up_table   [    row] = unpack_col(    row) ^ unpack_col(    result);
        col_down_table [rev_row] = unpack_col(rev_row) ^ unpack_col(rev_result);
    }
}

static inline board_t execute_move_0(board_t board) {
    board_t ret = board;
    board_t t = transpose(board);
    ret ^= col_up_table[(t >>  0) & ROW_MASK] <<  0;
    ret ^= col_up_table[(t >> 16) & ROW_MASK] <<  4;
    ret ^= col_up_table[(t >> 32) & ROW_MASK] <<  8;
    ret ^= col_up_table[(t >> 48) & ROW_MASK] << 12;
    return ret;
}

static inline board_t execute_move_1(board_t board) {
    board_t ret = board;
    board_t t = transpose(board);
    ret ^= col_down_table[(t >>  0) & ROW_MASK] <<  0;
    ret ^= col_down_table[(t >> 16) & ROW_MASK] <<  4;
    ret ^= col_down_table[(t >> 32) & ROW_MASK] <<  8;
    ret ^= col_down_table[(t >> 48) & ROW_MASK] << 12;
    return ret;
}

static inline board_t execute_move_2(board_t board) {
    board_t ret = board;
    ret ^= board_t(row_left_table[(board >>  0) & ROW_MASK]) <<  0;
    ret ^= board_t(row_left_table[(board >> 16) & ROW_MASK]) << 16;
    ret ^= board_t(row_left_table[(board >> 32) & ROW_MASK]) << 32;
    ret ^= board_t(row_left_table[(board >> 48) & ROW_MASK]) << 48;
    return ret;
}

static inline board_t execute_move_3(board_t board) {
    board_t ret = board;
    ret ^= board_t(row_right_table[(board >>  0) & ROW_MASK]) <<  0;
    ret ^= board_t(row_right_table[(board >> 16) & ROW_MASK]) << 16;
    ret ^= board_t(row_right_table[(board >> 32) & ROW_MASK]) << 32;
    ret ^= board_t(row_right_table[(board >> 48) & ROW_MASK]) << 48;
    return ret;
}

/* Execute a move. */
static inline board_t execute_move(int move, board_t board) {
    switch(move) {
    case 0: // up
        return execute_move_0(board);
    case 1: // down
        return execute_move_1(board);
    case 2: // left
        return execute_move_2(board);
    case 3: // right
        return execute_move_3(board);
    default:
        return ~0ULL;
    }
}

static inline int get_max_rank(board_t board) {
    int maxrank = 0;
    while (board) {
        maxrank = std::max(maxrank, int(board & 0xf));
        board >>= 4;
    }
    return maxrank;
}

/* Optimizing the game */

struct eval_state {
    trans_table_t trans_table; // transposition table, to cache previously-seen moves
    float cprob_thresh;
    int maxdepth;
    int curdepth;
    int cachehits;
    int moves_evaled;

    eval_state() : cprob_thresh(0), maxdepth(0), curdepth(0), cachehits(0), moves_evaled(0) {
    }
};

// score a single board heuristically
static float score_heur_board(board_t board);
// score a single board actually (adding in the score from spawned 4 tiles)
static float score_board(board_t board);
// score over all possible moves
static float score_move_node(eval_state &state, board_t board, float cprob);
// score over all possible tile choices and placements
static float score_tilechoose_node(eval_state &state, board_t board, float cprob);


static float score_helper(board_t board, const float* table) {
    return table[(board >>  0) & ROW_MASK] +
           table[(board >> 16) & ROW_MASK] +
           table[(board >> 32) & ROW_MASK] +
           table[(board >> 48) & ROW_MASK];
}

static float score_heur_board(board_t board) {
    return score_helper(          board , heur_score_table) +
           score_helper(transpose(board), heur_score_table) +
           100000.0f;
}

static float score_board(board_t board) {
    return score_helper(board, score_table);
}

static float score_tilechoose_node(eval_state &state, board_t board, float cprob) {
    int num_open = count_empty(board);
    cprob /= num_open;

    float res = 0.0f;
    board_t tmp = board;
    board_t tile_2 = 1;
    while (tile_2) {
        if ((tmp & 0xf) == 0) {
            res += score_move_node(state, board |  tile_2      , cprob * 0.9f) * 0.9f;
            res += score_move_node(state, board | (tile_2 << 1), cprob * 0.1f) * 0.1f;
        }
        tmp >>= 4;
        tile_2 <<= 4;
    }
    return res / num_open;
}

// Statistics and controls
// cprob: cumulative probability
// don't recurse into a node with a cprob less than this threshold
static const float CPROB_THRESH_BASE = 0.0001f;
static const int CACHE_DEPTH_LIMIT  = 3;
static const int SEARCH_DEPTH_LIMIT = 4;

static float score_move_node(eval_state &state, board_t board, float cprob) {
    if (cprob < state.cprob_thresh || state.curdepth >= SEARCH_DEPTH_LIMIT) {
        if(state.curdepth > state.maxdepth)
            state.maxdepth = state.curdepth;
        return score_heur_board(board);
    }

    if(state.curdepth < CACHE_DEPTH_LIMIT) {
        const trans_table_t::iterator &i = state.trans_table.find(board);
        if(i != state.trans_table.end()) {
            state.cachehits++;
            return i->second;
        }
    }

    float best = 0.0f;
    state.curdepth++;
    for (int move = 0; move < 4; ++move) {
        board_t newboard = execute_move(move, board);
        state.moves_evaled++;

        if (board != newboard) {
            best = std::max(best, score_tilechoose_node(state, newboard, cprob));
        }
    }
    state.curdepth--;

    if (state.curdepth < CACHE_DEPTH_LIMIT) {
        state.trans_table[board] = best;
    }

    return best;
}

static float _score_toplevel_move(eval_state &state, board_t board, int move) {
    //int maxrank = get_max_rank(board);
    board_t newboard = execute_move(move, board);

    if(board == newboard)
        return 0;

    state.cprob_thresh = CPROB_THRESH_BASE;

    return score_tilechoose_node(state, newboard, 1.0f) + 1e-6;
}

float score_toplevel_move(board_t board, int move) {
    float res;
    struct timeval start, finish;
    double elapsed;
    eval_state state;

    gettimeofday(&start, NULL);
    res = _score_toplevel_move(state, board, move);
    gettimeofday(&finish, NULL);

    elapsed = (finish.tv_sec - start.tv_sec);
    elapsed += (finish.tv_usec - start.tv_usec) / 1000000.0;

//    printf("Move %d: result %f: eval'd %d moves (%d cache hits, %d cache size) in %.2f seconds (maxdepth=%d)\n", move, res,
//        state.moves_evaled, state.cachehits, (int)state.trans_table.size(), elapsed, state.maxdepth);

    return res;
}

/* Find the best move for a given board. */
int find_best_move_original(board_t board) {
    int move;
    float best = 0;
    int bestmove = -1;

//    print_board(board);
//    printf("Current scores: heur %.0f, actual %.0f\n", score_heur_board(board), score_board(board));

    for(move=0; move<4; move++) {
        float res = score_toplevel_move(board, move);

        if(res > best) {
            best = res;
            bestmove = move;
        }
    }

    return bestmove;
}

int ask_for_move(board_t board) {
    int move;
    char validstr[5];
    char movestr[64];

    const char *allmoves = "UDLR";
    char *validpos = validstr;

    print_board(board);

    for(move=0; move<4; move++) {
        if(execute_move(move, board) != board)
            *validpos++ = "UDLR"[move];
    }
    *validpos = 0;
    if(validpos == validstr)
        return -1;

    while(1) {
//        printf("Move [%s]? ", validstr);

        if(!fgets(movestr, sizeof(movestr)-1, stdin))
            return -1;

        if(!strchr(validstr, toupper(movestr[0]))) {
//            printf("Invalid move.\n");
            continue;
        }
        break;
    }
    return strchr(allmoves, toupper(movestr[0])) - allmoves;
}

/* Playing the game */
static board_t draw_tile() {
    return (unif_random(10) < 9) ? 1 : 2;
}

static board_t insert_tile_rand(board_t board, board_t tile) {
    int index = unif_random(count_empty(board));
    board_t tmp = board;
    while (true) {
        while ((tmp & 0xf) != 0) {
            tmp >>= 4;
            tile <<= 4;
        }
        if (index == 0) break;
        --index;
        tmp >>= 4;
        tile <<= 4;
    }
    return board | tile;
}

static board_t initial_board() {
    board_t board = draw_tile() << (4 * unif_random(16));
    return insert_tile_rand(board, draw_tile());
}

void play_game(get_move_func_t get_move) {
	uint16_t xboard[SIZE][SIZE];

	std::fstream frecord("./record.txt", std::ios_base::out);

	printf("\033[?25l\033[2J\033[H");


	// register signal handler for when ctrl-c is pressed
	signal(SIGINT, signal_callback_handler);

    board_t board = initial_board();
    convert(board, xboard);
    int scorepenalty = 0; // "penalty" for obtaining free 4 tiles
	drawBoard(xboard,score_board(board) - scorepenalty );
	setBufferedInput(false);
    int moveno = 0;


    while(1) {
        int move;
        board_t newboard;

        for(move = 0; move < 4; move++) {
            if(execute_move(move, board) != board)
                break;
        }
        if(move == 4)
            break; // no legal moves



        move = get_move(board);
        if(move < 0)
            break;

        if (move == 0){
            printf("\nMove #%d, moving   left\n", ++moveno);
        }
        else if (move == 1){
            printf("\nMove #%d, moving  right\n", ++moveno);
        }
        else if (move == 2){
            printf("\nMove #%d, moving     up\n", ++moveno);
        }
        else{
            printf("\nMove #%d, moving   down\n", ++moveno);
        }
        newboard = execute_move(move, board);


        board_t tile = draw_tile();
        if (tile == 2) scorepenalty += 4;
        board = insert_tile_rand(newboard, tile);
        convert(board, xboard);
    	drawBoard(xboard,score_board(board) - scorepenalty);

    	frecord << moveno << " , " << score_board(board) - scorepenalty << std::endl;
    }

    frecord.close();
	setBufferedInput(true);

	printf("\033[?25h");

    // print_board(board);
    printf("\nGame over. Your score is %.0f. The highest rank you achieved was %d.\n", score_board(board) - scorepenalty, get_max_rank(board));
}

//******************************  Random Walk AI
bool movesAvailable(board_t board) {
		int move;
        for(move = 0; move < 4; move++) {
            if(execute_move(move, board) != board)
                break;
        }
        return (move < 4);
}	


bool DEBUG = false;
int RUNS;
time_t startTime;

board_t randomRun(board_t board, int move) {
	board_t orig = board;
	board_t newboard = execute_move(move, board);
	if (newboard == board) {
		return 0;
	}
	board = insert_tile_rand(newboard, draw_tile());		

	// run til we can't
	while (true) {
		if (!movesAvailable(board)) break;
		
		if (get_max_rank(board)>get_max_rank(orig)) break; // this is an optimization to run faster. The assumption is that if we created a new max rank all is good again.
		
		board_t newboard = execute_move(unif_random(4), board);
		if (newboard == board) continue;
		board = insert_tile_rand(newboard, draw_tile());
	}
	return board;
}
	
float MAX;
float MIN;	
int LEVELUP_COUNT;
int ACTUAL_COUNT;
int deepSearch = 0;
int origRuns = 0;

float multiRandomRun(board_t board, int move, int runs) {
	float total = 0.0;
	float max = 0;
	float min = 10000000000;
	board_t max_b, min_b;
//	float* scores = new float[runs];	
	LEVELUP_COUNT = 0;
	ACTUAL_COUNT = 0;
	
	for (int i=0 ; i < runs ; i++) {
		board_t endboard = randomRun(board, move);
		float s = score_board(endboard);
//		printf("%d - %lf\n", move_list[0], s);

//		if (get_max_rank(board)<get_max_rank(endboard)) s*=10000;
		if (s==0) continue; // illegal move
		ACTUAL_COUNT++;
		
		total += s;
		if (s>max) {
			max = s;
			max_b = endboard;
		}
		if (s<min) {
			min = s;
			min_b = endboard;
		}

		if (get_max_rank(board)<get_max_rank(endboard)) LEVELUP_COUNT++; // count getting a new max rank

	}
//	float avg = total / runs;
	if (ACTUAL_COUNT==0) ACTUAL_COUNT=1; // to avoid dev be 0
	float avg = total / ACTUAL_COUNT;	
	
	MAX = max;
	MIN = min;
/*	
	std::sort(scores, scores+runs);

	total = 0;
	int starti = runs*50/100;
	for (int i=starti ; i < runs ; i++) {
		total += scores[i];
	}
	float result = total/(runs-starti);

	return result;
*/	
//	return -1;

//	delete[] scores;
	
	return avg; //17
//	return max;  // 12
//	return (avg+max)/2;   //18 21
//	return (2*avg+max)/3;   //21
//	return (avg+3*max)/4;   //16 13

}


/* Find the best move for a given board. */
int find_best_move_montecarlo(board_t board) {
		float bestScore = 0; 
		int bestMove = -1;
		int bestMoveListInedex = -1;
		float bestMax, bestMin;
		int levelUpCount = 0;
		int actualRuns = 0;
		
		if (origRuns==0) origRuns=RUNS;
		
		if ((deepSearch>0) && (get_max_rank(board)>deepSearch)) {
			deepSearch = 0;
			RUNS = origRuns;
//			printf("Deep Search End\n");
		}

		for (int i=0;i<4;i++) {
			// score move position
			float score = multiRandomRun(board, i, RUNS);
//			if ((depth == 0) && (moveRes.score > 64)) {console.log('limit reached');}
//			if (score < 0) console.log('bugggg');
			
			if (score >= bestScore) {
				bestScore = score;
				bestMove = i;
				bestMax = MAX;
				bestMin = MIN;
				levelUpCount = LEVELUP_COUNT;
				actualRuns = ACTUAL_COUNT;
			}
			
			// Deep search. If we touched a new max rank, look deeper because we are close to the critical stages.
			if ((LEVELUP_COUNT > 0) && (get_max_rank(board)>10) && (deepSearch==0)) {
				deepSearch = get_max_rank(board);
				i = 0;
				bestScore = 0;
				RUNS = 1000000;
//				printf("Deep Search Start\n");
				continue;
			}
		}
		
		// assert move found		
		if (bestMove == -1) {
			printf("ERROR...");
			exit(1);
		} 

		if (DEBUG) {		
//			printf(" (%20lu %20f %d) Chosen move %d ", board, score_board(board), get_max_rank(board), bestMove);
//			printf(". [UC %8d|%8d] Search Score %20f | MAX %20f MIN %20f \n", levelUpCount, actualRuns, bestScore, bestMax, bestMin);
		}
		
//		printf("Chosen move - %d. End score %f(%d)\n", bestMove, bestScore, get_max_rank(board));
		return bestMove;
}

int find_best_move(board_t board) {return find_best_move_montecarlo(board);}

int main(int argc, char **argv) {
    init_tables();


	RUNS = 10000;
	if (argc>1) {
		RUNS = atoi(argv[1]);
	}	
	if (argc>2) {
		DEBUG = true;	
	}
	DEBUG = true;
	
//    play_game(find_best_move_montecarlo);
	play_game(find_best_move_original);
}




//***********************************************************************************************************
// ALTERNATIVE VERSIONS
// multi depth version
#if 0
bool DEBUG = false;
const int MAXDEPTH = 10;
int MOVE_LIST_LEN;
int MOVES_LEN;
int RUNS;
time_t startTime;

typedef int move_list_t[MAXDEPTH];
typedef move_list_t moves_t[1<<(MAXDEPTH*2)];
static moves_t moves_table;

void prepare_moves_table(int depth) {
	MOVE_LIST_LEN = depth;
	MOVES_LEN = 1<<(depth*2);
	
	for (int l=0; l<MOVE_LIST_LEN; l++) {
		int blocksize = 1<<(2*(l)); //4^(l+1);
		int digit = 0;
		int c = 0;
		for (int i=0;i < MOVES_LEN; i++) {
			moves_table[i][l] = digit;
			
			c++;
			if (c==blocksize) {
				digit = (digit + 1) % 4;
				c = 0;
			}
		}
	}
}

board_t randomRun(board_t board, move_list_t move_list) {
	board_t orig = board;
	for (int i=0; i<MOVE_LIST_LEN;i++) {
		board_t newboard = execute_move(move_list[i], board);
//		if (newboard == board) return score_board(board)-1; // to fix a rare usecase where a move exists but doesn't add value. in this case a non existant move would return the same score leading to an illegal result.
		if (newboard == board) {
			return 0;
//			if (i==0) return 0;
//			continue;
		}
		board = insert_tile_rand(newboard, draw_tile());		
	}	
	
		
//board_t newboard = execute_move(move, board);		
//board = insert_tile_rand(board, draw_tile());
	
	// run til we can't
	while (true) {
		if (!movesAvailable(board)) break;
		if (get_max_rank(board)>get_max_rank(orig)) break;
		
		board_t newboard = execute_move(unif_random(4), board);
		if (newboard == board) continue;
		board = insert_tile_rand(newboard, draw_tile());
	}
	return board;
}
	
float MAX;
float MIN;	
int LEVELUP_COUNT;
int ACTUAL_COUNT;
int deepSearch = 0;
int origRuns = 0;

float multiRandomRun(board_t board, move_list_t move_list, int runs) {
	float total = 0.0;
	float max = 0;
	float min = 10000000000;
	board_t max_b, min_b;
	
//	float* scores = new float[runs];
	LEVELUP_COUNT = 0;
	ACTUAL_COUNT = 0;
	
	for (int i=0 ; i < runs ; i++) {
		board_t endboard = randomRun(board, move_list);
		float s = score_board(endboard);
//		printf("%d - %lf\n", move_list[0], s);

//		if (get_max_rank(board)<get_max_rank(endboard)) s*=10000;
		if (s==0) continue;
		ACTUAL_COUNT++;
		
		total += s;
		if (s>max) {
			max = s;
			max_b = endboard;
		}
		if (s<min) {
			min = s;
			min_b = endboard;
		}

		if (get_max_rank(board)<get_max_rank(endboard)) LEVELUP_COUNT++;
		
//		scores[i] = s;
	}
//	float avg = total / runs;
	if (ACTUAL_COUNT==0) ACTUAL_COUNT=1; // to avoid devistion be 0
	float avg = total / ACTUAL_COUNT;	
/*
	printf("**tested move list ");
	for (int i=0; i<MOVE_LIST_LEN;i++) {
		printf(" %d", move_list[i]);
	}
	printf(". Score %f (legal %d)\n", score_board(board), board!=execute_move(move_list[0], board));	
*/
	
	MAX = max;
	MIN = min;
//	if (get_max_rank(max_b)==13) MAX += 0.1;
/*	
	std::sort(scores, scores+runs);

	total = 0;
	int starti = runs*50/100;
	for (int i=starti ; i < runs ; i++) {
		total += scores[i];
	}
	float result = total/(runs-starti);

	return result;
*/	
//	return -1;

//	delete[] scores;
	
	return avg; //17
//	return max;  // 12
//	return (avg+max)/2;   //18 21
//	return (2*avg+max)/3;   //21
//	return (avg+3*max)/4;   //16 13

}


/* Find the best move for a given board. */
int find_best_move_depth(board_t board) {
		float bestScore = 0; 
		int bestMove = -1;
		int bestMoveListInedex = -1;
		float bestMax, bestMin;
		int levelUpCount = 0;
		int actualRuns = 0;
		
		if (origRuns==0) origRuns=RUNS;
		
		if ((deepSearch>0) && (get_max_rank(board)>deepSearch)) {
			deepSearch = 0;
			RUNS = origRuns;
			printf("Deep Search End\n");
		}

		for (int i=0;i<MOVES_LEN;i++) {
			// score move position
			float score = multiRandomRun(board, moves_table[i], RUNS);
//			if ((depth == 0) && (moveRes.score > 64)) {console.log('limit reached');}
//			if (score < 0) console.log('bugggg');
			
			if (score >= bestScore) {
				bestScore = score;
				bestMove = moves_table[i][0];
				bestMoveListInedex = i;
				bestMax = MAX;
				bestMin = MIN;
				levelUpCount = LEVELUP_COUNT;
				actualRuns = ACTUAL_COUNT;
			}
			
			if ((LEVELUP_COUNT > 0) && (get_max_rank(board)>10) && (deepSearch==0)) {
				deepSearch = get_max_rank(board);
				i = 0;
				bestScore = 0;
				RUNS = 1000000;
				printf("Deep Search Start\n");
				continue;
			}
		}
		
		// assert move found		
		if (bestMove == -1) {
			printf("ERROR...");
			exit(1);
		} 

		if (DEBUG) {		
			printf(" (%20llu %20f %d) Chosen move %d ( move list ", board, score_board(board), get_max_rank(board), bestMove);
			for (int i=0; i<MOVE_LIST_LEN;i++) {
				printf(" %d", moves_table[bestMoveListInedex][i]);
			}
			printf("). Score [%8d|%8d] %20f  | MAX %20f MIN %20f \n", levelUpCount, actualRuns, bestScore, bestMax, bestMin);			
		}
		
		
//		printf("Chosen move - %d. End score %f(%d)\n", bestMove, bestScore, get_max_rank(board));
		return bestMove;
}




//*************************************
// markov chain version
//********************************************
void qsort(float a[], int pr[], int lo, int hi) 
{
  int h, l, prp;
  float p,t;

  if (lo < hi) {
    l = lo;
    h = hi;
    p = a[hi];
	prp = pr[hi];

    do {
      while ((l < h) && (a[l] <= p)) 
          l = l+1;
      while ((h > l) && (a[h] >= p))
          h = h-1;
      if (l < h) {
          t = a[l];
          a[l] = a[h];
          a[h] = t;
          t = pr[l];
          pr[l] = pr[h];
          pr[h] = t;

      }
    } while (l < h);

    a[hi] = a[l];
    a[l] = p;
    pr[hi] = pr[l];
    pr[l] = prp;

    qsort( a, pr, lo, l-1 );
    qsort( a, pr, l+1, hi );
  }
}

class Avg {
	int count=0;
	float total=0;
	
	void zero() {count=0; total=0;}
	void add(float v) {count++; total+=v;}
	int getCount() {return count;}
	float getTotal() {return total;}
	float getAvg() {if (count>0) return total/count; else return 0;}
};

class ScoreNode {
	private:
	int depth;
	int availCount[16]; //index is 2^^4 bitwise or of availablity of the 4 moves.

	// running total and count of runs ending in this node. if its a leaf node, it can be a run that went on. If its a non-leaf its a run that actually ended here.
	int hitCount; 
	float runningTotal; 
	
	public:	
	ScoreNode* next[4]; //pointers to next level nodes for the 4 moves.	
	int nextCount[4];
	
	static ScoreNode* createTree(int depth); // create a node tree of given depth
	void zeroTree(); // zero out the entire tree
	
	void processBoard(board_t board); // inc the availCounter for the given board.
	void processEndScore(float score); //accumilate the score data
	void processMove(int move) {nextCount[move]++;}
	float calcScore(int* bestMove); // return the node's score.
	
	void printState();
};

ScoreNode* ScoreNode::createTree(int depth) {
	ScoreNode* n = new ScoreNode();
	for (int i=0;i<4;i++) {
		if (depth > 0) {
			n->next[i] = createTree(depth-1);
		} else {
			n->next[i] = NULL;
		}
	}
	n->depth = depth;
	return n;
}

void ScoreNode::zeroTree() {
	for (int i=0;i<16;i++) {
		availCount[i] = 0;
	}
	hitCount = 0;
	runningTotal = 0;

	for (int i=0;i<4;i++) {
		if (next[i]) next[i]->zeroTree();
		nextCount[i] = 0;
	}
}

void ScoreNode::processBoard(board_t board) {
	int bitField = 0;
	int bitValue = 1;
	// build bit field
	for (int i=0;i<4;i++) {
		if (execute_move(i, board) != board) { // if can move
			bitField += bitValue;			
		}
		bitValue *= 2;
	}
	
	availCount[bitField]++;
}

void ScoreNode::processEndScore(float score) {
	hitCount++;
	runningTotal += score;
}


float ScoreNode::calcScore(int* bestMove) {

	if (!next[0]) { // isLeaf
		if (hitCount == 0) return 0;
		float score = runningTotal/hitCount;
		return score;
	}

	if (hitCount != availCount[0]) printf("error4534");	

	float scores[4];
	float scores_sort[4];
	float scoreSum=0;
	for (int i=0;i<4;i++) {
		scores[i] = next[i]->calcScore(NULL);
		scores_sort[i] = scores[i];
		scoreSum += scores[i];
	}

/*	
	printf("\ncalcScore %d - ", depth);
	for (int i=0;i<4;i++) {
		printf("%f ", scores[i]);
	}
*/	
	
	// sort scores and find permuation
	int perm[4] = {0,1,2,3};
	qsort(scores_sort, perm, 0, 3);
/*
	for (int i=0;i<4;i++) {
		printf("%d ", perm[i]);
	}
*/	
	
	int total = 0;
	int pcount[4] = {0,0,0,0}; //pcount[0] is the hit count for the best move. pcount[1] is the hit count for the second best where the best is not possible, etc.
	int bitField[4] = {1,2,4,8};
//	printf("DEADEND %d\n", availCount[0]);	
	for (int i=1;i<16;i++) { // start from 1. 0 is end game
		int best;
		for (best=3;best>=0;best--) {
			if ((i&bitField[perm[best]]) > 0) break; // if current best bit is on for i, break
		}
		if (best == -1) {printf("ERRROR3\n");}
		
		// check if scarse
		for (int j=0;j<4;j++) {
//			printf("|%d %d %d|", (i&bitField[j]), availCount[i], scores[j]);
			if (((i&bitField[j]) > 0) && (availCount[i] > 0) && (scores[j]==0)) {
//				printf("scarse");
				// return regular avg
				float score = 0;
				total = 0;
				for (int i=0;i<4;i++) {
					score += scores[i]*nextCount[i];
					total += nextCount[i];
				}	
				score += runningTotal;
				total += hitCount;
				score /= total;
				return score;
			}
		}
		
		pcount[perm[best]] += availCount[i]; // add count to correct bucket
		total += availCount[i];
//		printf("%d->%d (%d)\n", i, perm[best], availCount[i]);
	}
	total += availCount[0]; // not added before

/*	
	printf("pcount - ");
	for (int i=0;i<4;i++) {
		printf("[%d %f] ", pcount[i], scores[i]);
	}
*/	
	
	float score=0; //weighted average of scores
	for (int i=0;i<4;i++) { 
		score += scores[i]*pcount[i]/total;
	}
	
	// add dead end
	score += runningTotal/total;
	
	if (total==0) score=0;
/*	
	printf(" total - %d score - %f", total, score);
	printf("\n");	
*/	
	if (bestMove) *bestMove = perm[3];
	return score;
}




void ScoreNode::printState() {
	printf("%*s", 30-depth, " ");
	
	printf("%d--> : [Score %d->%8f]", depth, hitCount, runningTotal/hitCount);
	if (next[0]) {
		for (int i=0;i<16;i++) {
			printf("[%d>%5d]", i, availCount[i]);
		}		
	
		for (int i=0;i<4;i++) {
			if (next[i]) {
				printf("\n (nextCount %d) ", nextCount[i]);
				next[i]->printState();
			}
		}
	}

}

ScoreNode* scoreNode;
/* Find the best move for a given board. */
int find_best_move_markov(board_t origBoard) {
	scoreNode->zeroTree();

	ScoreNode* leaf = scoreNode;
	for (int x=0;x<RUNS;x++) {
		ScoreNode* n = scoreNode; // start at the top
		board_t board = origBoard;
		
		while (true) {
			if (n) {
				n->processBoard(board);
			}
			
			if (!movesAvailable(board)) break;
			
			int move;
			board_t newboard;
			while(true) {
				move = unif_random(4);
				newboard = execute_move(move, board);
				if (newboard != board) break; // try again. poor man's next move...
			}
			board = insert_tile_rand(newboard, draw_tile()); // finish move
//printf("*move %d ", move);
			if (n) {
				n->processMove(move);
				n = n->next[move];
				if (n) {
					leaf = n; // make leaf point to last node in tree
				}
			}
			
//			if (get_max_rank(board)>get_max_rank(origBoard)) break; 			
			if (get_max_rank(board)==13) printf("GOT 13!!!\n");
		}
		// run is finnished. add score
		float score = score_board(board);
		leaf->processEndScore(score);
//printf(" done* %f\n", score);		
	}
	
//	scoreNode->printState();
	
	int move;
	float score = scoreNode->calcScore(&move);
 printf(" done* %f %d\n", score, move);			
/*
	if (DEBUG) {		
		printf(" (%20llu %20f %d) Chosen move %d \n", origBoard, score_board(origBoard), get_max_rank(origBoard), move);

	}
*/

	return move;
}


int main(int argc, char **argv) {
    init_tables();

	int depth = 3;
	if (argc>1) {
	   depth = atoi(argv[1]);
	}

	RUNS = 10000;
	if (argc>2) {
		RUNS = atoi(argv[2]);
	}	
	if (argc>3) {
		DEBUG = true;	
	}

	
	scoreNode = ScoreNode::createTree(depth);
	prepare_moves_table(depth);	
	
	// Choose between the two variants here
    play_game(find_best_move_depth);	
    //play_game(find_best_move_markov);
}

#endif






