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

vector<vector<int>> dp;
int n, mn = 0;
vector<int> arr;

int f(int i, int val){
    int acutal_val = val + mn;
    if(i == n - 2){
        return 1 + (acutal_val != 0);
    }
    int &ans = dp[i][val];
    if(ans != -1)
        return ans;
    ans = f(i + 1, arr[i + 1] + acutal_val - mn);
    if(acutal_val)
        ans = (ans + f(i + 1, arr[i + 1] - acutal_val - mn)) % mod;
    return ans;
}

void solve()
{
    cin >> n;
    arr.resize(n);
    int sum = 0;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        if(i < n - 1 and i > 0)
            mn = min(mn, arr[i] - sum);
        if(i)
            sum += arr[i];
    }
    dp.resize(n, vector<int>(sum - mn + 10, -1));
    cout << f(1, arr[1] - mn) << endl;
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