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
int n;
vector<int> arr, pref;
vector<vector<int>> dp;

int f(int i, int j){
    if(i > j)
        return 0;

    int &ans = dp[i][j];
    if(ans != -inf)
        return ans;

    ans = max(arr[i] + (pref[j] - pref[i]) - f(i + 1, j)
        , arr[j] + (pref[j - 1] - pref[i - 1]) - f(i, j - 1));

    return ans;
}

void solve()
{
    cin >> n;
    arr.resize(n + 1);
    pref.resize(n + 1);
    dp.assign(n + 1, vector<int> (n + 1, -inf));
    pref[0] = 0;

    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        pref[i] = pref[i - 1] + arr[i];
    }

    cout << 2 * f(1, n) - pref[n] << endl;
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