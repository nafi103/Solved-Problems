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
    int n, q;
    cin >> n >> q;
    vector<int> arr(n + 1), ini(n + 1), turn_p2(n + 1), extra(n + 1);
    ini[0] = turn_p2[0] = extra[0] = 0;
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        ini[i] = ini[i - 1] + log2(arr[i]);
        if((arr[i] & (arr[i] - 1)) == 0){
            extra[i] = 0;
        }else{
            extra[i] = 1;
            int tmp = (arr[i] >> 1);
            turn_p2[i] = ((tmp & (tmp - 1)) == 0);
        }
        extra[i] += extra[i - 1];
        turn_p2[i] += turn_p2[i - 1];
    }
    while(q--){
        int l, r;
        cin >> l >> r;
        int convertable = turn_p2[r] - turn_p2[l - 1];
        int extra_give = extra[r] - extra[l - 1];
        int converted = (convertable + 1) / 2;
        cout << ini[r] - ini[l - 1] + (extra_give - converted) << endl;
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