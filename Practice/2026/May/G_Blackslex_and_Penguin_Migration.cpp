#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
// #define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int query(int i, int j){
    cout << "? " << i << " " << j << endl;
    cin >> j;
    return j;
}

pair<int,int> equation_solver(int x1, int y1, int d1, int x2, int y2, int d2){
    int x_plus_y = d1 + 2; // x - x1 + y - y1 = d1
    int x_minus_y = d2 - y2 + x2; // x - x2 + y2 - y = d2
    int x = (x_plus_y + x_minus_y) / 2;
    int y = x_plus_y - x;
    return {x, y};
}

void solve()
{
    int n;
    cin >> n;
    vector<pair<int,int>> d1;
    int r = n * n;
    for(int i = 2; i <= r; i++){
        d1.push_back({query(1, i), i});
    }

    sort(all(d1), greater<pair<int,int>>());
    int x1 = 1, y1 = 1, c1 = d1[0].second; // first corner found

    d1.clear();
    vector<int> possible_adj;
    for(int i = 1; i <= r; i++){
        if(i == c1)
            continue;
        int dis = query(c1, i);
        d1.push_back({dis, i});
        if(dis == n - 1){
            possible_adj.push_back(i);
        }
    }
    // d1 contains distance to all other cell of c1
    // found the opposite corner of c1
    vector<pair<int,int>> dis_rand;
    for(int i = 1; i < n; i++){
        dis_rand.push_back({query(possible_adj[0], possible_adj[i]), possible_adj[i]});
    }
    sort(all(dis_rand), greater<pair<int,int>>());
    int x2 = 1, y2 = n, c2 = dis_rand[0].second;

    vector<vector<int>> grid(n + 1, vector<int> (n + 1));
    grid[x1][y1] = c1;
    grid[x2][y2] = c2;

    vector<pair<int,int>> a, b;
    for(auto &[d, id]: d1){
        if(id == c2)
            continue;
        a.push_back({id, d});
    }
    for(int i = 1; i <= r; i++){
        if(i == c1 or i == c2)
            continue;
        b.push_back({i, query(i, c2)});
    }

    sort(all(a));
    sort(all(b));

    for(int i = 0; i < r - 2; i++){
        auto [x, y] = equation_solver(x1, y1, a[i].second, x2, y2, b[i].second);
        grid[x][y] = a[i].first;
    }

    cout << "!" << endl;
    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= n; j++){
            cout << grid[i][j] << " \n"[j == n];
        }
    }
    cout.flush();
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}