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

int n, l, k;
vector<int> d,a,suff;
vector<vector<int>> dp;

void input(){
    cin >> n >> l >> k;
    d.resize(n); a.resize(n); suff.resize(n);
    dp.assign(n, vector<int> (k + 1, -1));
    for(int i = 0; i < n; i++)
        cin >> d[i];
    for(int i = 0; i < n; i++)
        cin >> a[i];
    suff[n - 1] = (l - d[n - 1]) * a[n - 1];
    for(int i = n - 2; i >= 0; i--){
        suff[i] = (d[i + 1] - d[i]) * a[i];
        suff[i] += suff[i + 1];
    }
}

int f(int i, int j){
    if(j == 0)
        return suff[i];
    int &ans = dp[i][j];
    if(ans != -1)
        return ans;
    ans = inf;
    for(int z = i + 1; z < n and z - i - 1 <= j; z++){
        ans = min(ans, f(z, j - (z - i - 1)) + (d[z] - d[i]) * a[i]);
    }
    if(j >= n - i - 1)
        ans = min(ans, (l - d[i]) * a[i]);
    return ans;
}

void solve()
{
    input();
    cout << f(0 , k) << endl;
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