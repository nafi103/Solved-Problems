#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
int I(int x){
    cout << "I " << x << endl;
    cin >> x;
    return x;
}
 int Q(int x){
    int ans;
    cout << "Q " << x << endl;
    cin >> ans;
    return ans;
}
 void solve()
{
    int n;
    cin >> n;
    cout << 0 << endl;
    //{0}
    int curr_size = I(0);
    if(curr_size == 1){
        // Only possible is AND, S = {0}
        int c = 0;
        for(int i = 0; i < n; i++){
            int new_size = I(1ll << i);
            if(new_size > curr_size)
                c |= (1ll << i);
            curr_size = new_size;
        }
        cout << "A " << 1 << " " << c << endl;
    }else{
        // Must be OR/XOR, S = {0, c}
        //Finding c using binary search (n operation)
        int c, l = 1, r = (1ll << n) - 1;
        while(l <= r){
            int mid = (l + r) / 2;
            if(Q(mid)){
                c = mid;
                l = mid + 1;
            }else{
                r = mid - 1;
            }
        }
        // c is found, two operations remaining
        curr_size = I((1ll << n) - 1);
        if(curr_size == 2){
            // S = {0, c}, Here c is 2 ** n - 1
            int new_size = I(1);
            if(new_size > curr_size){
                cout << "A " << 3 << " " << c << endl;
            }else{
                cout << "A " << 2 << " " << c << endl;
            }
            return;
        }
        if(Q((1ll << n) - 1)){
            cout << "A " << 2 << " " << c << endl;
        }else{
            cout << "A " << 3 << " " << c << endl;
        }
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