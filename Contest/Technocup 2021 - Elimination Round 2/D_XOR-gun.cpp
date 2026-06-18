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
    int n;
    cin >> n;
    int arr[n + 1], pxor[n + 1];
    arr[0] = pxor[0] = 0;
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        pxor[i] = (pxor[i - 1] ^ arr[i]);
    }
    int ans = inf;
    bool found = false;
    for(int i = 2; i <= n; i++){
        for(int j = i; j <= n; j++){
            int xr = (pxor[j] ^ pxor[j - i]);
            if(j > i and xr < arr[j - i]){
                ans = min(ans, i - 1);
                found = true;
            }
            if(j < n and arr[j + 1] < xr){
                ans = min(ans, i - 1);
                found = true;
            }
            int l = j - i + 1, r = j;
            while(l < r){
                int left = pxor[l] ^ pxor[j - i];
                int right = pxor[r] ^ pxor[l];
                if(left > right){
                    ans = min(ans, i - 2);
                    found = true;
                }
                l++;
            }
        }
        if(found)
            break;
    }
    if(!found)
        cout << -1 << endl;
    else
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