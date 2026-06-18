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
 int dx[] = {1, -1, 0, 0};
int dy[] = {0, 0, 1, -1};
 int n, m;
vector<vector<int>> grid, pref_1, pref_2;
vector<vector<bool>> visited;
vector<bool> visited_row, visited_column;
 bool valid(int i, int j){
    return i >= 0 and i < n and j >= 0 and j < m and grid[i][j] == 1 and !visited[i][j];
}
 void dfs(int i, int j){
    visited[i][j] = true;
    visited_row[i] = true;
    visited_column[j] = true;
    for(int k = 0; k < 4; k++){
        int ni = i + dx[k], nj = j + dy[k];
        if(valid(ni, nj))
            dfs(ni, nj);
    }
}
 void solve()
{
    char c;
    cin >> n >> m;
    // pref_1 -> up-down, pref_2 -> left-right
    grid.assign(n, vector<int>(m, 0));
    pref_1.resize(n, vector<int>(m));
    pref_2 = pref_1;
    visited_row.assign(n, false);
    visited_column.assign(m, false);
    for(int i = 0; i < n; i++){
        for(int j = 0; j < m; j++){
            cin >> c;
            if(c == '#')
                grid[i][j] = 1;
            pref_1[i][j] = pref_2[i][j] = grid[i][j];
            if(i)
                pref_1[i][j] += pref_1[i - 1][j];
            if(j)
                pref_2[i][j] += pref_2[i][j - 1];
        }
    }
    for(int i = 0; i < n; i++){
        for(int j = 0; j < m; j++){
            if(grid[i][j] == 0){
                int up = pref_1[i][j], down = pref_1[n - 1][j] - pref_1[i][j];
                int left = pref_2[i][j], right = pref_2[i][m - 1] - pref_2[i][j];
                if((up and down) or (left and right)){
                    cout << -1 << endl;
                    return;
                }
            }
        }
    }
    int ans = 0;
    visited.assign(n, vector<bool>(m, false));
    for(int i = 0; i < n; i++){
        for(int j = 0; j < m; j++){
            if(valid(i, j)){
                ans++;
                dfs(i, j);
            }
        }
    }
    if(n - accumulate(all(visited_row), 0ll) and m - accumulate(all(visited_column), 0ll) == 0
        or n - accumulate(all(visited_row), 0ll) == 0 and m - accumulate(all(visited_column), 0ll))
        cout << -1 << endl;
    else
        cout << ans << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}