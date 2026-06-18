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
    vector<int> arr(n), d(n), ans(n, -1);
    for(int i = 0; i < n; i++)
        cin >> arr[i];
    for(int i = 0; i < n; i++)
        cin >> d[i];
    for(int i = n; i >= 1; i--){
        int b = -1;
        for(int j = 0; j < n; j++){
            if(d[j] == 0 and ans[j] == -1){
                b = j;
                break;
            }
        }
        if(b == -1){
            cout << -1 << endl;
            return;
        }
        ans[b] = i;
        for(int j = b - 1; j >= 0; j--){
            if(arr[b] > arr[j] and ans[b] > ans[j])
                d[j]--;
        }
    }
    for(int i = 0; i < n; i++){
        if(d[i]){
            cout << -1 << endl;
            return;
        }
    }
    for(int i = 0; i < n; i++){
        cout << ans[i] << " \n"[i == n - 1];
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