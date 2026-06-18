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
int a[N], b[N];
int n, k;
 void solve()
{
    cin >> n >> k;
    // vector<int> a(n), b(n);
    for(int i = 0; i < n; i++){
        cin >> a[i];
    }
    for(int i = 0; i < n; i++){
        cin >> b[i];
    }
    if(k == 1){
        for(int i = 0; i < n; i++){
            if(b[i] == -1)
                b[i] = a[i];
            if(a[i] != b[i]){
                cout << "NO" << endl;
                return;
            }
        }
        cout << "YES" << endl;
        return;
    }
    map<int,int> cnta, cntb;
    vector<bool> all_same(k, true);
    for(int i = 0; i < k; i++){
        for(int j = i + k; j < n; j += k){
            if(a[i] != a[j]){
                all_same[i] = false;
                break;
            }
        }
        if(!all_same[i]){
            for(int j = i; j < n; j += k){
                if(b[j] != -1 and b[j] != a[j]){
                    cout << "NO" << endl;
                    return;
                }
            }
        }else{
            cnta[a[i]]++;
            set<int> diff;
            for(int j = i; j < n; j += k){
                diff.insert(b[j]);
            }
            diff.erase(-1);
            if(sz(diff) > 1){
                cout << "NO" << endl;
                return;
            }
            if(diff.size() == 1){
                cntb[*diff.begin()]++; 
            }
        }
    }
    for(auto &[f, s]: cntb){
        if(s > cnta[f]){
            cout << "NO" << endl;
            return;
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
        solve ();
    }
}