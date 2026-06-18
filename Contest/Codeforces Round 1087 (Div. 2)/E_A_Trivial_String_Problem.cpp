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
 const int N = 1e6 + 10;
int dp[N], lps[N],n , q;
string str;
 void solve()
{
    cin >> n >> q;
    cin >> str;
    while(q--){
        int l, r;
        cin >> l >> r;
        l--, r--;
        // int ans = 0;
        lps[l] = l;
        for(int i = l + 1; i <= r; i++){
            int j = lps[i - 1];
            while(j > l and str[j] != str[i]){
                j = lps[j - 1];
            }
            lps[i] = j;
            if(str[i] == str[j])
                lps[i]++;
        }
        // for(int i = l; i <= r; i++){
        //     cerr << lps[i] << " \n"[i == r];
        // }
        int ans = 1;
        dp[l] = 1;
        for(int i = l + 1; i <= r; i++){
            if(lps[l] == lps[i])
                dp[i] = dp[l];
            else{
                dp[i] = dp[lps[i] - 1] + dp[i - (lps[i] - l)];
            }
            ans += dp[i];
        }
        // for(int i = l; i <= r; i++){
        //     cerr << dp[i] << " \n"[i == r];
        // }
        cout << ans << endl;
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