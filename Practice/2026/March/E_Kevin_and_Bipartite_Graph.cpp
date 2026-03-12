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
    if(2 * n <= m){
        cout << "NO" << endl;
        return;
    }
    cout << "YES" << endl;
    deque<int> d(2 * n);
    for(int i = 0; i < 2 * n; i++){
        d[i] = (i + 2) / 2;
    }
    vector<vector<int>> ans(2 * n, vector<int> (m));
    for(int j = 0; j < m; j++){
        for(int i = 0; i < 2 * n; i++){
            ans[i][j] = d[i];
        }
        int x = d.front();
        d.pop_front();
        d.push_back(x);
    }
    for(int i = 0; i < 2 * n; i++){
        for(int j = 0; j < m; j++){
            cout << ans[i][j] << (j == m - 1 ? '\n': ' ');
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}