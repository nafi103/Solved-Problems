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
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int N = 200005;
vector<int> val;
int arr[N],brr[N], n, m, last[N];
 bool is_prime(int n){
    for (int i = 2; i * i <= n; i++)
        if(n % i == 0)
            return false;
    return true;
}
 vector<vector<int>> dp;
 void solve()
{
    cin >> n;
    for (int i = 0; i < n; i++){
        cin >> arr[i];
    }
    for (int i = 0; i < n; i++){
        cin >> brr[i];
    }
    for (int i = 0; i < n; i++){
        for (int j = 0; j < m; j++)
            dp[i][j] = -1;
    }
    for (int i = 0; i < n; i++){
        int left = 1, right = 1;
        if (i)
            left = gcd(arr[i], arr[i - 1]);
        if (i < n - 1)
            right = gcd(arr[i], arr[i + 1]);
        int mx = lcm(left, right);
        if(mx <= brr[i])
            last[i] = mx;
        else
            last[i] = arr[i];
    }
    // for (int i = 0; i < n; i++){
    //     cerr << last[i] << " \n"[i == n - 1];
    // }
    for (int i = 0; i < n; i++){
        int l = 1;
        if(i)
            l = lcm(last[i - 1], l);
        if(i < n - 1)
            l = lcm(last[i + 1], l);
        // debug(l)
        int mx = 0, smx = 0;
        if(i){
            for(int j = 0; j < m; j++){
                if(dp[i - 1][j] >= mx){
                    smx = mx;
                    mx = dp[i - 1][j];
                }else if(dp[i - 1][j] > smx)
                    smx = dp[i - 1][j];
            }
        }
        dp[i][0] = mx;
        for (int j = 1; j < m; j++){
            if(last[i] != arr[i] and last[i] <= brr[i]){
                dp[i][0] = mx + 1;
                continue;
            }
            int new_val = last[i] * val[j];
            if(gcd(new_val, l) != last[i] or new_val == arr[i] or new_val > brr[i])
                dp[i][j] = dp[i][0];
            else if(new_val <= brr[i]){
                dp[i][j] = (i and dp[i - 1][j] == mx? smx: mx) + 1;
            }
        }
    }
    // for (int i = 0; i < n; i++){
    //     debug(dp[i]);
    // }
    int ans = 0;
    for (int j = 0; j < m; j++)
        ans = max(ans, dp[n - 1][j]);
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
    cin >> t;
    val.push_back(1);
    for (int i = 2; i <= 200; i++){
        if(is_prime(i))
            val.push_back(i);
    }
    m = sz(val);
    dp.assign(N, vector<int>(m, -1));
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}