#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
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
 /*
 * Fenwick Tree (1D)
 * 0-indexed implementation.
 * constructor(arr): O(N) linear time construction.
 * query(r): Returns the sum of elements in range [0, r].
 * query(l, r): Returns the sum of elements in range [l, r].
 * add(idx, delta): Adds delta to the element at idx.
 */
template <typename T>
struct Fenwick_Tree{
    int n;
    vector<T> bit;
     Fenwick_Tree(int _n) : n(_n), bit(_n, 0) {}
     Fenwick_Tree(const vector<T> &arr){
        n = sz(arr);
        bit.assign(n, 0);
        for (int i = 0; i < n; i++){
            bit[i] += arr[i];
            int r = i | (i + 1);
            if(r < n)
                bit[r] += bit[i];
        }
    }
     T query(int r) const {
        T sum = 0;
        for(; r >= 0; r = (r & (r + 1)) - 1)
            sum += bit[r];
        return sum;
    }
     T query(int l, int r) const {
        if(l > r)
            return 0;
        return query(r) - query(l - 1);
    }
     void add(int idx, T delta){
        for(; idx < n; idx = idx | (idx + 1)){
            bit[idx] += delta;
        }
    }
};
 void solve()
{
    int n, q, cnt = 0;
    cin >> n >> q;
    Fenwick_Tree<int> ft(q);
    vector<int> unread[n];
    vector<int> notification(q, 0);
    queue<int> qq;
    while(q--){
        int t;
        cin >> t;
        if(t == 1){
            int id;
            cin >> id;
            id--;
            unread[id].push_back(cnt);
            qq.push(cnt);
            notification[cnt]++;
            ft.add(cnt, 1);
            cnt++;
            cout << ft.query(cnt - 1) << endl;
        }else if(t == 2){
            int x;
            cin >> x;
            x--;
            while(!unread[x].empty()){
                int id = unread[x].back();
                unread[x].pop_back();
                ft.add(id, 0 - notification[id]);
                notification[id] = 0;
            }
            cout << ft.query(cnt - 1) << endl;
        }else{
            int r;
            cin >> r;
            r--;
            while(!qq.empty() and qq.front() <= r){
                int id = qq.front();
                qq.pop();
                ft.add(id, 0 - notification[id]);
                notification[id] = 0;
            }
            cout << ft.query(cnt - 1) << endl;
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}