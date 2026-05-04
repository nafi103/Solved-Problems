#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 26;
const int inf = 1e9;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int mt = 0;

struct Node{
    int value, in;

    Node(){
        value = inf;
        in = -1;
    }

    Node(int val, int _in){
        value = val;
        in = _in;
    }

    Node(int _in){
        value = inf;
        in = _in;
    }
};

Node merge(Node &left, Node &right){
    return Node(min(left.value, right.value), max(left.in, right.in));
}

struct Lazy_Segment_Tree{
    int n;
    vector<int> v, lazy;
    vector<Node> st;

    Lazy_Segment_Tree(string &s,int _n){
        n = _n;
        st.resize(4 * n);
        lazy.resize(4 * n,0);
        v.resize(n + 1);
        for(int i = 0; i < n; i++){
            v[i + 1] = s[i] - 'a';
        }
        build(1,1,n);
    }
    
    void build(int node, int b, int e){
        if(b == e){
            if(b == n)
                st[node] = Node(v[b]);
            else if(b == n - 1){
                if(v[b] == v[b + 1])
                    st[node] = Node(b + 1, v[b]);
                else
                    st[node] = Node(v[b]);
            }else{
                if(v[b] == v[b + 1])
                    st[node] = Node(b + 1, v[b]);
                else if(v[b] == v[b + 2])
                    st[node] = Node(b + 2, v[b]);
                else
                    st[node] = Node(v[b]);
            }
            return;
        }
        int mid = (b + e) / 2,left = 2 * node, right = 2 * node + 1;
        build(left, b, mid);
        build(right, mid + 1,e);
        st[node] = merge(st[left], st[right]);
    }
    
    void propagate(int node, int b, int e){
        if(lazy[node] == mt)
            return;
        if(b == e){
            st[node].in = (st[node].in + lazy[node]) % mod;
            v[b] = st[node].in;
        }
        if(b != e){
            lazy[2 * node] += lazy[node];
            lazy[2 * node + 1] += lazy[node];
        }
        lazy[node] = mt;
    }

    Node get(int node, int b, int e, int &i){
        propagate(node, b, e);
        if(e < i or b > i) return Node();
        if(b == e and b == i){
            return st[node];
        }
        int mid = (b+e) / 2,left = 2*node, right = 2*node+1;
        if(mid < i)
            return get(right, mid + 1, e, i);
        return get(left, b, mid, i);
    }

    Node get(int i){
        return get(1, 1, n, i);
    }

    void update(int node, int b, int e, int &i){
        propagate(node, b, e);
        if(b == e and b == i){
            Node next = get(b + 1), after_that = get(b + 2);
            if(st[node].in == next.in)
                st[node].value = b + 1;
            else if(st[node].in == after_that.in)
                st[node].value = b + 2;
            else
                st[node].value = inf;
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        if(mid >= i)
            update(left, b, mid, i);
        else
            update(right, mid + 1, e, i);
        st[node] = merge(st[left], st[right]);
    }

    void update(int i){
        update(1, 1, n, i);
    }
    
    void update(int node, int b, int e, int &l, int &r, int &value){
        propagate(node, b, e);
        if(e<l or b>r) return;
        if(b >= l and e <= r){
            lazy[node] += value;
            propagate(node, b, e);
            return;
        }
        int mid = (b + e) / 2,left = 2 * node, right = 2 * node + 1;
        update(left, b, mid, l, r, value);
        update(right, mid + 1, e, l, r, value);
        st[node] = merge(st[left], st[right]);
    }

    void update(int l, int r, int value){
        update(1, 1, n, l, r, value);
        if(l > 1)
            update(l - 1);
        if(l > 2)
            update(l - 2);
        update(r);
        if(r > l)
            update(r - 1);
    }
    
    Node query(int node, int b, int e, int &l, int &r){
        propagate(node, b, e);
        if(e<l or b>r) return Node();
        if(b>=l and e<=r){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2 * node + 1;
        Node qleft = query(left, b, mid, l, r), qright = query(right, mid + 1, e, l, r);
        return merge(qleft, qright);
    }

    int query(int l, int r){
        return query(1, 1, n, l, r).value;
    }
};

void solve()
{
    int n, q;
    cin >> n >> q;
    string str;
    cin >> str;
    Lazy_Segment_Tree st(str, n);
    while(q--){
        int t;
        cin >> t;
        if(t == 1){
            int l, r, val;
            cin >> l >> r >> val;
            st.update(l, r, val);
        }else{
            int l, r;
            cin >> l >> r;
            int id = st.query(l, r);
            if(id <= r)
                cout << "NO" << endl;
            else
                cout << "YES" << endl;
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