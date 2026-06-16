#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 2e11;

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
    string s;
    cin >> s;
    vector<int> arr(n), c(n);
    for(auto &x: arr)
        cin >> x;
    for(auto &x: c)
        cin >> x;

    int ps, change_id = -1;
    if(s[0] == '1'){
        if(c[0] != arr[0]){
            cout << "No" << endl;
            return;
        }
        ps = c[0];
    }else{
        arr[0] = c[0];
        ps = c[0];
    }

    for(int i = 1; i < n; i++){
        if(c[i] < c[i - 1]){
            cout << "No" << endl;
            return;
        }

        if(s[i] == '0'){
            if(c[i] == c[i - 1]){
                arr[i] = -inf;
                ps += arr[i];
                change_id = i;
            }else{
                arr[i] = c[i] - ps;
                ps = c[i];
                change_id = -1;
            }
        }else{
            if(c[i] > c[i - 1]){
                int prev_ps_must = c[i] - arr[i];

                int add = prev_ps_must - ps;

                if(add){
                    if(change_id == -1){
                        cout << "No" << endl;
                        return;
                    }

                    ps -= arr[change_id];
                    arr[change_id] += add;
                    ps += arr[change_id];
                }
                ps += arr[i];
                change_id = -1;
            }else{
                ps += arr[i];
            }

        }
    }

    int mx = -inf;
    ps = 0;

    for(int i = 0;i < n; i++){
        ps += arr[i];
        mx = max(mx, ps);

        if(mx > c[i]){
            cout << "No" << endl;
            return;
        }
    }

    cout << "Yes" << endl;
    for(int i = 0; i < n; i++){
        cout << arr[i] << " \n"[i == n - 1];
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