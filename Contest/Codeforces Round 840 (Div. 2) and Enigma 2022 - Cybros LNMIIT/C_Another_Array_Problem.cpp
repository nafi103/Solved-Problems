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
 const int N = 2e5 + 10;
int n, arr[N];
 void input(){
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }
}
 void solve()
{
    input();
    if(n > 3){
        cout << n * (*max_element(arr, arr + n)) << endl;
        return;
    }
    if(n == 3){
        cout << max({3 * arr[0], 3 * arr[2], arr[0] + arr[1] + arr[2],
            arr[0] + 2 * abs(arr[1] - arr[2]), arr[2] + 2 * abs(arr[0] - arr[1]),
                3 * max(abs(arr[0] - arr[1]), abs(arr[1] - arr[2]))}) << endl;
        return;
    }
    if(n == 2){
        cout << max(arr[0] + arr[1], 2 * abs(arr[0] - arr[1])) << endl;
        return;
    }
    cout << arr[0] << endl;
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