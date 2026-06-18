#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int N = 20;
int dp[N][(1 << 18)], n, final_mask;
int g[N][N];

void input(){
    memset(dp, -1, sizeof dp);
    int m, u, v;
    cin >> n >> m;
    final_mask = (1 << (n - 2)) - 1;
    for(int i = 0; i < m; i++){
        cin >> u >> v;
        u--, v--;
        g[u][v]++;
    }
}

int f(int node, int mask){
    if(mask == final_mask){
        return g[node][n - 1];
    }
    int &ans = dp[node][mask];
    if(ans != -1)
        return ans;
    ans = 0;
    for(int nbr = 1; nbr < n - 1; nbr++){
        if(g[node][nbr] == 0)
            continue;
        int nbrp = nbr - 1;
        if(mask & (1 << nbrp))
            continue;
        else{
            ans = (ans + g[node][nbr] * f(nbr, mask | (1 << nbrp))) % mod;
        }
    }
    return ans;
}

void solve()
{
    input();
    if(n == 2){
        cout << g[0][1] << endl;
        return;
    }
    cout << f(0, 0) << endl;
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