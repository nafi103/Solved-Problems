#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
 using namespace std;
using namespace chrono;
using namespace __gnu_pbds;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
const __int128_t inf = 2e18 + 100; // Use a cap larger than h
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 // BUG FIX 1: This sum must be 1 + 2 + ... + n
__int128_t ap_sum_1_to_n(int n) {
    if (n <= 0) return 0;
    // Use __int128_t to prevent overflow during intermediate calculation
    return (__int128_t)n * (n + 1) / 2;
}
  void solve()
{
    int n, p_ll, h_ll; // Use long long for input
    cin >> n >> p_ll >> h_ll;
        __int128_t p = p_ll;
    __int128_t h = h_ll;
     vector<int> mul, add;
    int attack = 0;
        for(int i = 0; i < n; i++){
        char t;
        cin >> t;
        if(t == '!')
            attack++;
        else{
            int val;
            cin >> val;
            if(t == '*')
                mul.push_back(val);
            else
                add.push_back(val);
        }
    }
     __int128_t ssum = 0;
    for(int x : add) ssum += x;
     if (attack == 0 || (p == 0 && ssum == 0)) {
        cout << "*" << endl;
        return;
    }
        sort(rbegin(add), rend(add));
    sort(rbegin(mul), rend(mul));
    while(!mul.empty() && mul.back() == 1)
        mul.pop_back();
        if (ssum == 0 && mul.empty()) {
        if (p == 0) {
             cout << "*" << endl;
             return;
        }
        __int128_t attacks_needed = (h + p - 1) / p;
        __int128_t full_rounds = (attacks_needed - 1) / attack;
        __int128_t remaining_attacks = attacks_needed - full_rounds * attack;
        cout << (long long)(full_rounds * n + remaining_attacks) << endl;
        return;
    }
      int op = 0; // Operation (turn) count
     if (mul.empty()) {
        // --- CASE 1: Add and Attack cards only ---
        // Strategy: Power-up, then attack.
        // Round k: Power = P + k*S. Damage = attack * (P + k*S)
        // Total damage after k rounds: Sum[i=1 to k] (attack * (P + i*S))
        // = attack * (k*P + S * (1+2+...+k))
        // = attack * (k*P + S * k*(k+1)/2)
                int l = 1, r = 2e9; // 2e9 is a safe upper bound
        int k = r + 1;      // k = min rounds to win
         while (l <= r) {
            int mid_k = l + (r - l) / 2; // mid_k = k rounds
            // BUG FIX 2: Use correct arithmetic sum formula
            __int128_t damage = (__int128_t)attack * p * mid_k;
            damage += (__int128_t)attack * ssum * ap_sum_1_to_n(mid_k);
                        if (damage >= h || damage < 0) { // check for overflow (negative)
                k = mid_k;
                r = mid_k - 1;
            } else {
                l = mid_k + 1;
            }
        }
                // We win on round `k`. So, we simulate `k-1` full rounds.
        op = (k - 1) * n;
        // Damage done in k-1 rounds
        __int128_t damage_done = (__int128_t)attack * p * (k - 1);
        // BUG FIX 2 (cont.): Use correct sum here too
        damage_done += (__int128_t)attack * ssum * ap_sum_1_to_n(k - 1); 
                h -= damage_done;
        p += (__int128_t)ssum * (k - 1); // New power at start of round k
     } else {
        // --- CASE 2: Multiply cards exist ---
        // Strategy: Power-up, then attack.
        // P_new = (P_old + ssum) * M
        // Damage = attack * P_new
        // P_next_round = P_new
                for(int i = 0; i < 100; i++){
            __int128_t new_p = p + ssum;
            // Cap power at a level that guarantees a win to avoid overflow
            if (new_p > h) new_p = h + 1; 
                        for(auto &x: mul){
                if (x > 0 && new_p > inf / x) new_p = inf; // Check overflow
                else new_p *= x;
                if (new_p > h) { new_p = h + 1; break; }
            }
            if (new_p > inf) new_p = inf; // Ensure it's capped
             // Check if we win this round
            __int128_t round_damage = 0;
            if (attack > 0 && new_p > inf / attack) round_damage = inf;
            else round_damage = new_p * attack;
             if (new_p >= h || round_damage >= h)
                break; // Will win in this round, break to final sim
                        // If power didn't change (e.g., p=0, ssum=0, but mul has cards), break.
            if (new_p == p) break; 
                        // BUG FIX 3: Apply "Power-up, then attack" logic
            // 1. Deal damage with the new power
            h -= round_damage;
            // 2. Set power for the start of the next round
            p = new_p;
            // 3. Add turns for this completed round
            op += n;
        }
    }
     // --- FINAL ROUND SIMULATION ---
    int mn = n + 1; 
     vector<__int128_t> add_pref(sz(add) + 1, 0);
    for(int i = 0; i < sz(add); i++) {
        add_pref[i+1] = add_pref[i] + add[i];
    }
     vector<__int128_t> mul_pref(sz(mul) + 1, 1);
    for(int i = 0; i < sz(mul); i++) {
        // Cap products to avoid overflow, (h+1) is enough
        if (mul_pref[i] > h + 1 || (mul[i] > 0 && mul_pref[i] > inf / mul[i])) mul_pref[i+1] = inf;
        else mul_pref[i+1] = mul_pref[i] * mul[i];
    }
     // BUG FIX 4: Removed "continue" and redundant extra loop.
    // This now correctly checks all combinations, including i=0, j=0.
    for(int i = 0; i <= sz(add); i++) { // i = number of Add cards
        for(int j = 0; j <= sz(mul); j++) { // j = number of Mul cards
            for(int k = 1; k <= attack; k++) { // k = number of Attack cards
                                __int128_t current_p = p + add_pref[i];
                if (current_p > inf) current_p = inf;
                 __int128_t m = mul_pref[j];
                                __int128_t damage;
                if (m > 0 && current_p > inf / m) damage = inf;
                else damage = current_p * m;
                 if (k > 0 && damage > inf / k) damage = inf;
                else damage = damage * k;
                 if(damage >= h){
                    mn = min(mn, i + j + k);
                }
            }
        }
    }
        cout << (long long)(op + mn) << endl;
}
 int32_t main()
{
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t; 
    for(int z = 1; z <= t; z++){
        solve();
    }
}