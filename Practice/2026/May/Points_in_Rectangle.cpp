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

template <typename T>
struct Fenwick_Tree2D {
    vector<vector<T>> bit;
    int n, m;

    Fenwick_Tree2D(int _n, int _m){
        n = _n;
        m = _m;
        bit.assign(n, vector<T>(m, 0));
    }

    Fenwick_Tree2D(const vector<vector<T>> &a) : Fenwick_Tree2D(sz(a), sz(a) > 0 ? sz(a[0]) : 0){
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < m; j++) {
                bit[i][j] += a[i][j];
                int r_col = j | (j + 1);
                if (r_col < m)
                    bit[i][r_col] += bit[i][j];
            }
        }

        for (int j = 0; j < m; j++) {
            for (int i = 0; i < n; i++) {
                int r_row = i | (i + 1);
                if (r_row < n)
                    bit[r_row][j] += bit[i][j];
            }
        }
    }

    T query(int x, int y) const {
        T ret = 0;
        for (int i = x; i >= 0; i = (i & (i + 1)) - 1)
            for (int j = y; j >= 0; j = (j & (j + 1)) - 1)
                ret += bit[i][j];
        return ret;
    }

    T query(int x1, int y1, int x2, int y2) const {
        T ret = 0;
        ret += query(x2, y2);
        ret -= query(x1 - 1, y2);
        ret -= query(x2, y1 - 1);
        ret += query(x1 - 1, y1 - 1);
        return ret;
    }

    void add(int x, int y, T delta) {
        for (int i = x; i < n; i = i | (i + 1))
            for (int j = y; j < m; j = j | (j + 1))
                bit[i][j] += delta;
    }
};

void solve()
{
    int q;
    cin >> q;
    vector<vector<int>> grid(1001, vector<int> (1001, 0));
    Fenwick_Tree2D<int> ft(1001, 1001);
    while(q--){
        int t;
        cin >> t;
        if(t == 0){
            int x, y;
            cin >> x >> y;
            int delta = 1 - grid[x][y];
            grid[x][y] += delta;
            ft.add(x, y, delta);
        }else{
            int x1, y1, x2, y2;
            cin >> x1 >> y1 >> x2 >> y2;
            cout << ft.query(x1, y1, x2, y2) << endl;
        }
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        cout<<"Case "<<z<<":\n";
        solve();
    }
}