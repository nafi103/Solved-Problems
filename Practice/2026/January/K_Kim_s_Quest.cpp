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

const int N = 2e5 + 2;
int dp[N][4][2][2], a[N], n;

int f(int i, int len, int last, int prev){
    if(i == n)
        return len == 0;
    int &ans = dp[i][len][last][prev];
    if(ans != -1)
        return ans;
    ans = f(i + 1, len, last, prev);
    if(len <= 1){
        if((prev + last + a[i]) % 2 == 0)
            ans = (ans + f(i + 1, 0, prev, a[i])) % mod;
    }else{
        ans = (ans + f(i + 1, len - 1, prev, a[i])) % mod;
    }
    return ans;
}

void solve()
{
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> a[i];
        a[i] %= 2;
    }
    memset(dp, -1, sizeof dp);
    cout << f(0, 3, 0, 0) << endl;
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