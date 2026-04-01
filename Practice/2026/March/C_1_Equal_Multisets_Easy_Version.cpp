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
int a[N], b[N], n, k;

void solve()
{
    cin >> n >> k;
    for(int i = 0; i < n; i++){
        cin >> a[i];
    }
    for(int i = 0; i < n; i++){
        cin >> b[i];
    }
    for(int i = 0; i < n - k; i++){
        if(!(a[i] == b[i] or b[i] == -1)){
            cout << "NO" << endl;
            return;
        }
    }
    for(int i = k; i < n; i++){
        if(!(a[i] == b[i] or b[i] == -1)){
            cout << "NO" << endl;
            return;
        }
    }
    multiset<int> available;
    int cnt = 0;
    for(int i = n - k; i < k; i++){
        if(b[i] == -1)
            cnt++;
        else
            available.insert(b[i]);
    }
    for(int i = n - k; i < k; i++){
        if(available.count(a[i])){
            available.erase(available.find(a[i]));
        }else{
            if(cnt == 0){
                cout << "NO" << endl;
                return;
            }else{
                cnt--;
            }
        }
    }
    cout << "YES" << endl;
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