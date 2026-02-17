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
int n, ans[N], b[N/2], id[N];

struct Segment_Tree{
    vector<int> st, v;
    int n;

    Segment_Tree(int _n){
        n = _n;
        st.resize(4 * n);
        v.resize(n + 1);
        v[0] = 0;
        for(int i = 1; i <= n; i++){
            v[i] = b[n - i + 1];
        }
        build(1, 1, n);
    }

    void build(int node, int be, int en){
        if(be == en){
            st[node] = v[be];
            return;
        }
        int mid = (be + en) / 2, left = node * 2, right = node * 2 + 1;
        build(left, be, mid);
        build(right, mid + 1, en);
        st[node] = max(st[left], st[right]);
    }

    void clear(int node, int be, int en, int &id){
        if(be == en){
            st[node] = -1;
            return;
        }
        int mid = (be + en) / 2, left = node * 2, right = node * 2 + 1;
        if(id <= mid)
            clear(left, be, mid, id);
        else
            clear(right, mid + 1, en, id);
        st[node] = max(st[left], st[right]);
    }

    int query(int node, int be, int en, int l, int r){
        if(be > r or en < l)
            return -1;
        if(l <= be and r >= en)
            return st[node];
        int mid = (be + en) / 2, left = node * 2, right = node * 2 + 1;
        return max(query(left, be, mid, l, r), query(right, mid + 1, en, l, r));
    }

    int find(int &val){
        int l = 1, r = n;
        while(l <= r){
            int mid = (l + r) / 2;
            if(query(1, 1, n, 1, mid) < val)
                l = mid + 1;
            else
                r = mid - 1;
        }
        clear(1, 1, n, l);
        return b[n - l + 1];
    }
};

void input(){
    cin >> n;
    for(int i = 1; i <= n / 2; i++){
        cin >> b[i];
        ans[2 * i] = b[i];
        id[b[i]] = 2 * i;
    }
}

void solve()
{
    input();
    Segment_Tree st(n / 2);
    set<int> s;
    for(int i = 1; i <= n; i++)
        s.insert(i);
    for(int i = 1; i <= n / 2; i++)
        s.erase(b[i]);
    while(sz(s)){
        int val = *s.rbegin();
        s.erase(val);
        int target = st.find(val);
        if(target == 0){
            cout << -1 << endl;
            return;
        }else{
            ans[id[target] - 1] = val;
        }
    }
    for(int i = 1; i <= n; i++)
        cout << ans[i] << (i == n ? '\n' : ' ');
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