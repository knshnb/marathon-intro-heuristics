#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <random>
#include <vector>
using Int = int;  // clang-format off
#define REP_(i, a_, b_, a, b, ...) for (Int i = (a), lim##i = (b); i < lim##i; i++)
#define REP(i, ...) REP_(i, __VA_ARGS__, __VA_ARGS__, 0, __VA_ARGS__)
#define ALL(v) std::begin(v), std::end(v)
struct SetupIO { SetupIO() { std::cin.tie(nullptr), std::ios::sync_with_stdio(false), std::cout << std::fixed << std::setprecision(13); } } setup_io;
#ifndef dump
#define dump(...)
#endif  // clang-format on

/**
 *    author:  knshnb
 *    created: Sun Jun 28 20:59:50 JST 2020
 **/

template <class T> bool chmin(T& a, const T& b) { return a > b ? a = b, true : false; }
template <class T> bool chmax(T& a, const T& b) { return a < b ? a = b, true : false; }

uint64_t rnd() {
    static uint64_t x = std::mt19937(std::chrono::steady_clock::now().time_since_epoch().count())();
    x += 0x9e3779b97f4a7c15;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
    x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
    return x ^ (x >> 31);
}

struct Timer {
    std::chrono::system_clock::time_point start_time;
    Timer() : start_time(std::chrono::system_clock::now()) {}
    double operator()() {
        return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now() - start_time)
            .count();
    }
};

constexpr Int D = 365;
constexpr Int K = 26;
Int s[D][K], c[K];
Int sum;
constexpr double TIME_LIMIT = 1980;

struct Schedule {
    std::array<Int, D> a;
    Int score = 0;
    Int calc_score(Int D_ = D) const {
        Int ret = 0;
        Int cur_minus = 0;
        static std::array<Int, K> last;
        REP(k, K) last[k] = -1;
        REP(d, D_) {
            cur_minus += sum - c[a[d]] * (d - last[a[d]]);
            ret += s[d][a[d]] - cur_minus;
            last[a[d]] = d;
        }
        return ret;
    }
    Schedule generate_neighbor() const {
        Schedule ret = *this;
        if (rnd() % 2) {
            Int dif = rnd() % 15 + 1;
            Int idx = rnd() % (D - dif);
            std::swap(ret.a[idx], ret.a[idx + dif]);
        } else {
            Int idx = rnd() % D;
            ret.a[idx] = rnd() % K;
        }
        ret.score = ret.calc_score();
        return ret;
    }
    void change1(Int d, Int k) {}
};

struct ScheduleDif : Schedule {
    std::array<std::vector<Int>, K> ds;
    ScheduleDif() {}
    ScheduleDif(const Schedule& sc) {
        score = sc.score, a = sc.a;
        REP(d, D) ds[sc.a[d]].push_back(d);
    }
    // a[d] <- k
    void change1(Int d, Int k) {
        if (a[d] == k) return;
        Int prv_k = a[d];
        a[d] = k;
        score += s[d][k] - s[d][prv_k];
        auto balance = [&d](auto& v, Int i) {
            auto calc = [](Int dif) { return dif * (dif - 1) / 2; };
            Int prv = i - 1 < 0 ? -1 : v[i - 1];
            Int nxt = i + 1 >= v.size() ? D : v[i + 1];
            return calc(d - prv) + calc(nxt - d) - calc(nxt - prv);
        };
        // erase d from st.ds[prv_k]
        {
            std::vector<Int>& v = ds[prv_k];
            auto i = std::lower_bound(v.begin(), v.end(), d) - v.begin();
            score += balance(v, i) * c[prv_k];
            // assert(v[i] == d);
            v.erase(v.begin() + i);
        }
        // insert d into st.ds[k]
        {
            std::vector<Int>& v = ds[k];
            auto i = std::lower_bound(v.begin(), v.end(), d) - v.begin();
            // assert(v[i] != d);
            v.insert(v.begin() + i, d);
            // assert(v[i] == d);
            score -= balance(v, i) * c[k];
        }
    }
};

Schedule greedy_initialize() {
    Schedule ret;
    std::array<Int, K> last;
    REP(k, K) last[k] = -1;
    REP(d, D) {
        Int ma = -1, use = -1;
        REP(k, K) {
            Int ad = s[d][k] + c[k] * (d - last[k]) + c[k] * 15;  // heuristic value function
            if (chmax(ma, ad)) use = k;
        }
        ret.a[d] = use;
        last[use] = d;
    }
    ret.score = ret.calc_score();
    return ret;
}

template <class State, bool use_dif = true> struct Annealing {
    constexpr static Int INF = 1e9;
    State cur;
    const double start_temp, end_temp;
    Timer timer;
    Annealing(State state, double start_temp_ = 50, double end_temp_ = 10)
        : cur(state), start_temp(start_temp_), end_temp(end_temp_) {}
    bool should_stay(Int score_dif, double cur_time, double time_lim) {
        double temperature = start_temp + (end_temp - start_temp) * cur_time / time_lim;
        double prob = std::exp(score_dif / temperature);
        return prob * INF < rnd() % INF;
    }
    bool update(double cur_time, double time_lim) {
        State nxt = cur.generate_neighbor();
        bool is_update = !should_stay(nxt.calc_score() - cur.calc_score(), cur_time, time_lim);
        if (is_update) {
            cur = std::move(nxt);
        }
        return is_update;
    }
    bool update_by_dif(double cur_time, double time_lim) {
        Int prv_score = cur.score;
        if (rnd() % 2 == 0) {
            // change 1 day
            Int d = rnd() % D, k = rnd() % K;
            Int prv_k = cur.a[d];
            while (k == prv_k) k = rnd() % K;
            bool is_update = !should_stay(cur.score_dif(d, k), cur_time, time_lim);
            if (is_update) {
                cur.change1(d, k);
            }
            return is_update;
        } else {
            // swap 2 days
            Int dif = rnd() % 15 + 1;
            Int d1 = rnd() % (D - dif), d2 = d1 + dif;
            while (cur.a[d1] == cur.a[d2]) dif = rnd() % 15 + 1, d1 = rnd() % (D - dif), d2 = d1 + dif;
            Int prv_k1 = cur.a[d1], prv_k2 = cur.a[d2];
            cur.change1(d1, prv_k2);
            cur.change1(d2, prv_k1);
            bool is_update = !should_stay(cur.score - prv_score, cur_time, time_lim);
            if (!is_update) {
                cur.change1(d1, prv_k1);
                cur.change1(d2, prv_k2);
            }
            return is_update;
        }
    }
    // return iteration num until time limit
    Int run(double time_lim) {
        for (Int t = 0;; t++) {
            double cur_time = timer();
            if (cur_time > time_lim) return t;
            Int prv_score = cur.score;
            if (use_dif) {
                update_by_dif(cur_time, time_lim);
            } else {
                update(cur_time, time_lim);
            }
            if (prv_score != cur.score) dump(t, prv_score, cur.score);
        }
    }
};

Int solve() {
    Timer timer;
    // input
    Int _;
    std::cin >> _;
    sum = 0;
    REP(i, K) std::cin >> c[i], sum += c[i];
    REP(i, D) REP(j, K) std::cin >> s[i][j];

    // local search
    Annealing<ScheduleDif, true> an(greedy_initialize(), 1500, 10);
    std::cerr << an.run(TIME_LIMIT - timer()) << " iterations\n";

    // output
    for (Int x : an.cur.a) std::cout << x + 1 << "\n";
    std::cout << std::endl;
    dump(an.cur.score);
    return an.cur.score + (Int)1e6;
}

signed main() {
#ifdef _LOCAL
    Int T = 10;
    Int score = 0;
    REP(i, T) {
        std::string filename = "data/";
        filename += ('0' + i);
        filename += ".txt";
        std::ifstream in(filename);
        std::cin.rdbuf(in.rdbuf());
        score += std::max(0, solve());
    }
    std::cerr << "sum : " << score << std::endl;
#else
    solve();
#endif
}
