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
 void solve()
{
    int n, m;
    cin >> n >> m;
    vector<vector<int>> grid(n, vector<int>(m)), pref = grid;
    for(int i = 0; i < n; i++){
        for(int j = 0; j < m; j++){
            cin >> grid[i][j];
            pref[i][j] = grid[i][j];
            if(i)
                pref[i][j] += pref[i - 1][j];
            if(j)
                pref[i][j] += pref[i][j - 1];
            if(i and j)
                pref[i][j] -= pref[i - 1][j - 1];
        }
    }
    int half = pref[n - 1][m - 1] / 2, other = pref[n - 1][m - 1] - half;
    int c = 0;
    while(pref[n - 1][c] < half)
        c++;
    int r = 0, sum = pref[n - 1][c];
    while(sum > half){
        sum -= grid[r][c];
        r++;
    }
    cout << half * other << endl;
    cout << string(c, 'R') << string(r, 'D') << 'R' << string(n - r, 'D') << string(m - c - 1, 'R') << endl;
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