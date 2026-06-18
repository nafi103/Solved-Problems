#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
/*
 * Fenwick Tree (1D)
 * 0-indexed implementation.
 * constructor(arr): O(N) linear time construction.
 * query(r): Returns the sum of elements in range [0, r].
 * query(l, r): Returns the sum of elements in range [l, r].
 * add(idx, delta): Adds delta to the element at idx.
 */
template <typename T>
struct Fenwick_Tree{
    int n;
    vector<T> bit;

    Fenwick_Tree(int _n) : n(_n), bit(_n, 0) {}

    T query(int r) const {
        T sum = 0;
        for(; r >= 0; r = (r & (r + 1)) - 1)
            sum += bit[r];
        return sum;
    }

    T query(int l, int r) const {
        if(l > r)
            return 0;
        return query(r) - query(l - 1);
    }

    void add(int idx, T delta){
        for(; idx < n; idx = idx | (idx + 1)){
            bit[idx] += delta;
        }
    }
};

void solve()
{
    int n, q;
    cin >> n >> q;

    Fenwick_Tree<int> row(q), column(q); // row -> column is 1, column -> row is 1
    vector<int> last_row(n, -1), last_column(n, -1);

    int black = 0;
    for(int i = 0, t, r, c; i < q; i++){
        cin >> t;

        if(t == 1){ // Row
            cin >> r;
            r--;
            if(last_row[r] == -1){
                black += n;
            }else{
                black += row.query(last_row[r], i - 1);
                column.add(last_row[r], -1);
            }
            column.add(i, 1);
            last_row[r] = i;
        }else{ // Columnn
            cin >> c;
            c--;
            if(last_column[c] == -1){
                black -= column.query(i - 1);
            }else{
                black -= column.query(last_column[c], i - 1);
                row.add(last_column[c], -1);
            }
            row.add(i, 1);
            last_column[c] = i;
        }

        cout << black << endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}