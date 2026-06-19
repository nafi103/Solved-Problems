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

bool check(array<int,3> &x, array<int,3> y){
    sort(all(y));
    return x == y;
}

void solve()
{
    int n, m;
    cin >> n >> m;
    vector<vector<int>> grid(n + 1, vector<int>(m + 1, 0)), pref = grid;
    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= m; j++){
            cin >> grid[i][j];
            pref[i][j] = grid[i][j] + pref[i - 1][j] + pref[i][j - 1] - pref[i - 1][j - 1];
        }
    }
    array<int, 3> target;
    cin >> target[0] >> target[1] >> target[2];
    sort(all(target));
    int ans = 0;
    for(int x1 = 1; x1 <= n - 2; x1++){
        for(int x2 = x1 + 1; x2 <= n - 1; x2++){
            int f1 = pref[x1][m], f2 = pref[x2][m] - f1, f3 = pref[n][m] - f1 - f2;
            if(check(target, {f1, f2, f3}))
                ans++;
        }
    }
    for(int y1 = 1; y1 <= m - 2; y1++){
        for(int y2 = y1 + 1; y2 <= m - 1; y2++){
            int f1 = pref[n][y1], f2 = pref[n][y2] - f1, f3 = pref[n][m] - f1 - f2;
            if(check(target, {f1, f2, f3}))
                ans++;
        }
    }
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
